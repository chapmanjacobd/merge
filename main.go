package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/alecthomas/kong"
	"golang.org/x/term"
)

type FileOverFileOpt string

const (
	SkipHash          FileOverFileOpt = "skip-hash"
	SkipSize          FileOverFileOpt = "skip-size"
	SkipLarger        FileOverFileOpt = "skip-larger"
	SkipSmaller       FileOverFileOpt = "skip-smaller"
	DeleteDestHash    FileOverFileOpt = "delete-dest-hash"
	DeleteDestSize    FileOverFileOpt = "delete-dest-size"
	DeleteDestLarger  FileOverFileOpt = "delete-dest-larger"
	DeleteDestSmaller FileOverFileOpt = "delete-dest-smaller"
	DeleteSrcHash     FileOverFileOpt = "delete-src-hash"
	DeleteSrcSize     FileOverFileOpt = "delete-src-size"
	DeleteSrcLarger   FileOverFileOpt = "delete-src-larger"
	DeleteSrcSmaller  FileOverFileOpt = "delete-src-smaller"
)

type FileOverFileMode string

const (
	FFSkip       FileOverFileMode = "skip"
	FFRenameSrc  FileOverFileMode = "rename-src"
	FFRenameDest FileOverFileMode = "rename-dest"
	FFDeleteSrc  FileOverFileMode = "delete-src"
	FFDeleteDest FileOverFileMode = "delete-dest"
)

type ConflictMode string

const (
	CSkip       ConflictMode = "skip"
	CRenameSrc  ConflictMode = "rename-src"
	CRenameDest ConflictMode = "rename-dest"
	CDeleteSrc  ConflictMode = "delete-src"
	CDeleteDest ConflictMode = "delete-dest"
	CMerge      ConflictMode = "merge"
)

type FileNode struct {
	Path      string
	IsDir     bool
	IsSymlink bool

	info       os.FileInfo
	infoLoaded bool
	mu         sync.Mutex
	sampleHash string
	fullHash   string
}

func (n *FileNode) GetInfo() (os.FileInfo, error) {
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.infoLoaded {
		return n.info, nil
	}
	info, err := os.Lstat(n.Path)
	if err != nil {
		return nil, err
	}
	n.info = info
	n.infoLoaded = true
	n.IsDir = info.IsDir()
	n.IsSymlink = info.Mode()&os.ModeSymlink != 0
	return n.info, nil
}

func (n *FileNode) GetSize() (int64, error) {
	info, err := n.GetInfo()
	if err != nil {
		return 0, err
	}
	return info.Size(), nil
}

func (n *FileNode) GetSampleHash(gap float64, stats *Stats) (string, error) {
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.sampleHash != "" {
		return n.sampleHash, nil
	}
	atomic.AddInt64(&stats.SampleHashes, 1)
	h, isFull, err := sampleHash(n.Path, gap)

	if err == nil {
		n.sampleHash = h
		if isFull {
			n.fullHash = h
		}
	}
	return h, err
}

func (n *FileNode) GetFullHash(stats *Stats) (string, error) {
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.fullHash != "" {
		return n.fullHash, nil
	}
	atomic.AddInt64(&stats.FullHashes, 1)
	h, err := computeFullHash(n.Path)

	if err == nil {
		n.fullHash = h
	}
	return h, err
}

func (n *FileNode) Clone(newPath string) *FileNode {
	n.mu.Lock()
	defer n.mu.Unlock()
	return &FileNode{
		Path:      newPath,
		IsDir:     n.IsDir,
		IsSymlink: n.IsSymlink,
	}
}

type FileOverFileStrategy struct {
	Optionals []FileOverFileOpt
	Required  FileOverFileMode
}

type MergeOperation struct {
	SrcPath         string
	DestPath        string
	RenamedDestPath string
	IsDir           bool
	Action          string // "skip", "delete-dest", "rename-src", "rename-dest", "transfer", "rename", "merge"
	DeleteDest      bool
	DeleteSrc       bool
	SrcNode         *FileNode
	SrcFS           *FileSystem
}

type FileSystem struct {
	mu      sync.RWMutex
	nodes   map[string]*FileNode
	checked map[string]bool
}

func NewFileSystem() *FileSystem {
	return &FileSystem{
		nodes:   make(map[string]*FileNode),
		checked: make(map[string]bool),
	}
}

func (fs *FileSystem) Add(path string, node *FileNode) {
	fs.mu.Lock()
	defer fs.mu.Unlock()
	fs.nodes[path] = node
	fs.checked[path] = true
}

func (fs *FileSystem) Get(path string) (*FileNode, bool) {
	fs.mu.RLock()
	defer fs.mu.RUnlock()
	node, ok := fs.nodes[path]
	return node, ok
}

func (fs *FileSystem) Exists(path string) bool {
	_, ok := fs.GetOrLoad(path)
	return ok
}

func (fs *FileSystem) Delete(path string) {
	fs.mu.Lock()
	defer fs.mu.Unlock()
	delete(fs.nodes, path)
	fs.checked[path] = true
}

func (fs *FileSystem) GetOrLoad(path string) (*FileNode, bool) {
	fs.mu.Lock()
	defer fs.mu.Unlock()

	if node, ok := fs.nodes[path]; ok {
		return node, true
	}
	if fs.checked[path] {
		return nil, false
	}

	// Lazy load
	info, err := os.Lstat(path)
	fs.checked[path] = true
	if err != nil {
		return nil, false
	}

	node := &FileNode{
		Path:       path,
		IsDir:      info.IsDir(),
		IsSymlink:  info.Mode()&os.ModeSymlink != 0,
		info:       info,
		infoLoaded: true,
	}
	fs.nodes[path] = node
	return node, true
}

type CLI struct {
	Paths       []string `arg:"" name:"paths" help:"Source [...] Destination" required:""`
	Sources     []string `kong:"-"`
	Destination string   `kong:"-"`

	FileOverFile   string `help:"File conflict strategy"`
	FileOverFolder string `help:"File over folder strategy" default:"merge"`
	FolderOverFile string `help:"Folder over file strategy" default:"merge"`

	Copy     bool `help:"Copy instead of move" short:"c"`
	Simulate bool `help:"Simulate without making changes" aliases:"dry-run" short:"n"`
	Workers  int  `help:"Number of parallel workers" default:"4" aliases:"threads" short:"j"`
	Verbose  int  `help:"Verbose output (0-2)" short:"v" type:"counter"`

	Ext       []string `help:"Filter by file extensions" short:"e"`
	Exclude   []string `help:"Exclude patterns" short:"E"`
	Include   []string `help:"Include patterns" short:"I"`
	Size      []string `help:"Filter by file size (fd-find syntax: -S+5M, -S-10M, -S5M%10)" short:"S" aliases:"sizes"`
	Limit     int      `help:"Limit number of files transferred" short:"l"`
	SizeLimit string   `help:"Limit total size of files transferred (e.g., 100M, 1G)" aliases:"sl"`

	RelativeTo string `help:"Preserve directory hierarchy relative to path"`
	Relative   bool   `help:"Shortcut for --relative-to=/"`

	Parent bool `help:"Include parent folder name" short:"P"`
	BSD    bool `help:"rsync/BSD mv behavior (src trailing slash matters)"`

	DestBSD    bool `help:"BSD destination mode (default)"`
	DestFolder bool `help:"Destination is always a folder" aliases:"folder" short:"t"`
	DestFile   bool `help:"Destination is a file (no-target-directory)" aliases:"file" short:"T"`

	Resume string `help:"Text file containing relative paths to process" short:"r" placeholder:"FILE"`
}

func (c *CLI) AfterApply() error {
	if c.FileOverFile == "" {
		if c.Copy {
			c.FileOverFile = "skip-hash rename-dest"
		} else {
			c.FileOverFile = "delete-src-hash rename-dest"
		}
	}

	if c.Relative {
		c.RelativeTo = "/"
	}

	if c.Ext != nil {
		// make sure all extensions start with a dot
		for i, ext := range c.Ext {
			if !strings.HasPrefix(ext, ".") {
				c.Ext[i] = "." + ext
			}
		}
	}

	if len(c.Paths) < 2 {
		return fmt.Errorf("at least one source and one destination directory are required")
	}
	c.Sources = c.Paths[:len(c.Paths)-1]
	c.Destination = c.Paths[len(c.Paths)-1]

	if c.DestFolder {
		info, err := os.Stat(c.Destination)
		if err == nil && !info.IsDir() {
			// Only error if strategies don't allow fixing this
			canFix := strings.Contains(c.FolderOverFile, "delete-dest") ||
				strings.Contains(c.FolderOverFile, "rename-dest") ||
				strings.Contains(c.FolderOverFile, "merge") ||
				strings.Contains(c.FileOverFile, "delete-dest") ||
				strings.Contains(c.FileOverFile, "rename-dest")

			if !canFix {
				return fmt.Errorf("destination %s exists but is not a directory, and conflict strategies do not allow replacement", c.Destination)
			}
		}
	}

	if c.DestFile && len(c.Sources) > 1 {
		return fmt.Errorf("cannot use --dest-file with multiple sources")
	}

	return nil
}

type MergeJob struct {
	Ops  []MergeOperation
	Root string
}

type Stats struct {
	FilesProcessed   int64
	FoldersProcessed int64
	Conflicts        int64
	BytesMoved       int64
	Errors           int64
	SampleHashes     int64
	FullHashes       int64
}

func (s *Stats) Print() {
	filesProcessed := atomic.LoadInt64(&s.FilesProcessed)
	foldersProcessed := atomic.LoadInt64(&s.FoldersProcessed)
	conflicts := atomic.LoadInt64(&s.Conflicts)
	bytesMoved := atomic.LoadInt64(&s.BytesMoved)
	sampleHashes := atomic.LoadInt64(&s.SampleHashes)
	fullHashes := atomic.LoadInt64(&s.FullHashes)
	errors := atomic.LoadInt64(&s.Errors)

	plural := "files"
	if filesProcessed == 1 {
		plural = "file"
	}
	fmt.Printf("\nSummary:\n")
	fmt.Printf("  %d %s processed\n", filesProcessed, plural)
	fmt.Printf("  %d folders\n", foldersProcessed)
	fmt.Printf("  %d conflicts\n", conflicts)
	fmt.Printf("  %d bytes moved\n", bytesMoved)
	if sampleHashes > 0 || fullHashes > 0 {
		fmt.Printf("  %d sample hashes, %d full hashes\n", sampleHashes, fullHashes)
	}
	if errors > 0 {
		fmt.Printf("  %d errors\n", errors)
	}
}

type Progress struct {
	start         time.Time
	lastPrintTime time.Time
	currentRel    atomic.Value // string
	termWidth     int
	mu            sync.Mutex
}

type Program struct {
	cli        *CLI
	stats      Stats
	progress   Progress
	sigChan    chan os.Signal
	sizeFilter func(int64) bool
}

func NewProgram(cli *CLI) *Program {
	p := &Program{
		cli:        cli,
		sigChan:    make(chan os.Signal, 1),
		sizeFilter: parseSizeFilter(cli.Size),
	}
	p.progress.start = time.Now()
	p.progress.lastPrintTime = time.Now()

	signal.Notify(p.sigChan, os.Interrupt, syscall.SIGTERM)
	p.watchResize()

	return p
}

func (p *Program) updateWidth() {
	w, _, err := term.GetSize(int(os.Stdout.Fd()))
	if err != nil {
		p.progress.termWidth = 80
		return
	}
	p.progress.mu.Lock()
	p.progress.termWidth = w
	p.progress.mu.Unlock()
}

func (p *Program) printProgress() {
	if p.cli.Verbose == 0 {
		return
	}

	files := atomic.LoadInt64(&p.stats.FilesProcessed)
	bytes := atomic.LoadInt64(&p.stats.BytesMoved)
	elapsed := time.Since(p.progress.start).Seconds()

	var rate float64
	if elapsed > 0 {
		rate = float64(bytes) / elapsed
	}

	status := fmt.Sprintf(
		"[Files: %d, %s] | %s/s",
		files,
		bytes2human(bytes),
		bytes2human(int64(rate)),
	)

	cur, _ := p.progress.currentRel.Load().(string)
	p.progress.mu.Lock()
	termWidth := p.progress.termWidth
	p.progress.mu.Unlock()

	remaining := termWidth - len(status) - 4
	if remaining > 10 && cur != "" {
		status += " | " + truncateMiddle(cur, remaining)
	}

	fmt.Fprint(os.Stderr, "\r"+status+"\033[K")
	p.progress.lastPrintTime = time.Now()
}

func bytes2human(n int64) string {
	const unit = 1024
	if n < unit {
		return fmt.Sprintf("%d B", n)
	}
	div, exp := int64(unit), 0
	for n >= unit*div && exp < 5 {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %ciB", float64(n)/float64(div), "KMGTPE"[exp])
}

func parseSizeFilter(sizes []string) func(int64) bool {
	if len(sizes) == 0 {
		return func(int64) bool { return true }
	}

	return func(size int64) bool {
		for _, constraint := range sizes {
			if !checkSizeConstraint(size, constraint) {
				return false
			}
		}
		return true
	}
}

func checkSizeConstraint(size int64, constraint string) bool {
	constraint = strings.TrimSpace(constraint)
	if constraint == "" {
		return true
	}

	// Handle percentage constraints (e.g., "5M%10" means 5MB ±10%)
	if strings.Contains(constraint, "%") {
		parts := strings.Split(constraint, "%")
		if len(parts) != 2 {
			return true // Invalid format, skip
		}
		targetSize := humanToBytes(parts[0])
		percent, err := strconv.ParseFloat(parts[1], 64)
		if err != nil {
			return true // Invalid percent, skip
		}
		lowerBound := int64(float64(targetSize) * (1 - percent/100))
		upperBound := int64(float64(targetSize) * (1 + percent/100))
		return size >= lowerBound && size <= upperBound
	}

	// Handle comparison operators
	if strings.HasPrefix(constraint, ">") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, ">"))
		return size > threshold
	}
	if strings.HasPrefix(constraint, "<") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "<"))
		return size < threshold
	}
	if strings.HasPrefix(constraint, "+") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "+"))
		return size > threshold
	}
	if strings.HasPrefix(constraint, "-") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "-"))
		return size <= threshold
	}

	// Exact match
	threshold := humanToBytes(constraint)
	return size == threshold
}

func truncateMiddle(s string, max int) string {
	if len(s) <= max {
		return s
	}
	if max < 3 {
		return s[:max]
	}
	half := (max - 1) / 2
	return s[:half] + "…" + s[len(s)-half:]
}

func (p *Program) updateCurrentFile(relPath string) {
	if p.cli.Verbose > 0 {
		p.progress.currentRel.Store(relPath)

		// Print progress every 200ms to avoid excessive updates
		now := time.Now()
		if now.Sub(p.progress.lastPrintTime) > 200*time.Millisecond {
			p.printProgress()
		}
	}
}

// sampleHash computes a hash from samples across the file for quick comparison.
// It returns the hash string, a boolean indicating if it's a full hash, and any error.
func sampleHash(path string, gap float64) (string, bool, error) {
	if gap <= 0 {
		gap = 0.1
	}

	f, err := os.Open(path)
	if err != nil {
		return "", false, err
	}
	defer f.Close()

	info, err := f.Stat()
	if err != nil {
		return "", false, err
	}

	size := info.Size()
	if size == 0 {
		return "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", true, nil // Empty file SHA256
	}

	h := sha256.New()
	chunkSize := int64(64 * 1024)

	if size <= chunkSize*10 {
		if _, err := io.Copy(h, f); err != nil {
			return "", false, err
		}
		return hex.EncodeToString(h.Sum(nil)), true, nil
	}

	positions := []int64{0}
	numSamples := int(1.0 / gap)
	for i := 1; i < numSamples; i++ {
		pos := (size * int64(i)) / int64(numSamples)
		// Ensure pos isn't overlapping with previous or next sample significantly
		positions = append(positions, pos)
	}
	positions = append(positions, size-chunkSize)

	// Clean up positions: unique and sorted
	posMap := make(map[int64]bool)
	var uniquePositions []int64
	for _, pos := range positions {
		if pos < 0 {
			pos = 0
		}
		if pos > size-chunkSize {
			pos = size - chunkSize
		}
		if !posMap[pos] {
			posMap[pos] = true
			uniquePositions = append(uniquePositions, pos)
		}
	}
	positions = uniquePositions

	buf := make([]byte, chunkSize)
	for _, pos := range positions {
		if _, err := f.Seek(pos, 0); err != nil {
			return "", false, err
		}

		n, err := f.Read(buf)
		if err != nil && err != io.EOF {
			return "", false, err
		}
		h.Write(buf[:n])
	}

	return hex.EncodeToString(h.Sum(nil)), false, nil
}

func humanToBytes(inputStr string) int64 {
	inputStr = strings.TrimSpace(strings.ToLower(inputStr))
	if inputStr == "" {
		return 0
	}

	reVal := regexp.MustCompile(`^[0-9.]*`)
	reUnit := regexp.MustCompile(`[a-z]+`)

	valStr := reVal.FindString(inputStr)
	unitStr := reUnit.FindString(inputStr)

	value, err := strconv.ParseFloat(valStr, 64)
	if err != nil {
		return 0
	}

	var k int64 = 1024
	byteMap := map[string]int64{
		"b": 1,
		"k": k,
		"m": k * k,
		"g": k * k * k,
		"t": k * k * k * k,
		"p": k * k * k * k * k,
	}

	unit := "m"
	if len(unitStr) > 0 {
		unit = string(unitStr[0])
	}

	multiplier, ok := byteMap[unit]
	if !ok {
		multiplier = k * k // default to MB
	}

	return int64(value * float64(multiplier))
}

func computeFullHash(path string) (string, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", err
	}
	defer f.Close()

	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		return "", err
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

func (p *Program) compareFiles(src, dst *FileNode) (bool, error) {
	srcSize, err := src.GetSize()
	if err != nil {
		return false, err
	}
	dstSize, err := dst.GetSize()
	if err != nil {
		return false, err
	}
	if srcSize != dstSize {
		return false, nil
	}

	srcSample, err := src.GetSampleHash(0.1, &p.stats)
	if err != nil {
		return false, err
	}
	dstSample, err := dst.GetSampleHash(0.1, &p.stats)
	if err != nil {
		return false, err
	}

	if srcSample != dstSample {
		return false, nil
	}

	srcFull, err := src.GetFullHash(&p.stats)
	if err != nil {
		return false, err
	}
	dstFull, err := dst.GetFullHash(&p.stats)
	if err != nil {
		return false, err
	}

	return srcFull == dstFull, nil
}

func (p *Program) streamScan(root string, fs *FileSystem) <-chan string {
	out := make(chan string, 1024)

	if p.cli.Resume != "" {
		if _, err := os.Stat(p.cli.Resume); err == nil {
			go func() {
				defer close(out)
				f, err := os.Open(p.cli.Resume)
				if err != nil {
					fmt.Fprintf(os.Stderr, "Error opening resume file: %v\n", err)
					return
				}
				defer f.Close()

				scanner := bufio.NewScanner(f)
				for scanner.Scan() {
					rel := scanner.Text()
					path := filepath.Join(root, rel)
					out <- path
				}
			}()
			return out
		}
	}

	go func() {
		defer close(out)
		filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
			if err != nil {
				return err
			}

			info, err := d.Info()
			if err != nil {
				return err
			}

			node := &FileNode{
				Path:       path,
				IsDir:      d.IsDir(),
				IsSymlink:  d.Type()&os.ModeSymlink != 0,
				info:       info,
				infoLoaded: true,
			}
			fs.Add(path, node)

			out <- path
			return nil
		})
	}()
	return out
}

func (p *Program) saveRemaining(srcRoot string, paths <-chan string) {
	name := p.cli.Resume
	if name == "" {
		name = filepath.Base(srcRoot) + ".remainingfiles"
	}
	f, err := os.Create(name)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to write remaining file: %v\n", err)
		return
	}
	defer f.Close()

	for path := range paths {
		rel, err := filepath.Rel(srcRoot, path)
		if err == nil {
			fmt.Fprintln(f, rel)
		} else {
			fmt.Fprintln(f, path)
		}
	}
	fmt.Fprintf(os.Stderr, "\nRemaining paths saved to: %s\n", name)
}

func getUniqueFilename(basePath string, fs *FileSystem) string {
	if !fs.Exists(basePath) {
		return basePath
	}
	dir := filepath.Dir(basePath)
	ext := filepath.Ext(basePath)
	base := filepath.Base(basePath)
	name := strings.TrimSuffix(base, ext)

	// Regex to find trailing _n
	re := regexp.MustCompile(`^(.*)_([0-9]+)$`)
	matches := re.FindStringSubmatch(name)

	baseName := name
	startIdx := 1
	if len(matches) == 3 {
		baseName = matches[1]
		val, _ := strconv.Atoi(matches[2])
		startIdx = val + 1
	}

	for i := startIdx; ; i++ {
		newPath := filepath.Join(dir, fmt.Sprintf("%s_%d%s", baseName, i, ext))
		if !fs.Exists(newPath) {
			return newPath
		}
	}
}

func parseFileOverFile(spec string) FileOverFileStrategy {
	parts := strings.Fields(spec)
	if len(parts) == 0 {
		return FileOverFileStrategy{Required: FFSkip}
	}

	strategy := FileOverFileStrategy{}
	required := parts[len(parts)-1]
	optionals := parts[:len(parts)-1]

	for _, opt := range optionals {
		strategy.Optionals = append(strategy.Optionals, FileOverFileOpt(opt))
	}
	strategy.Required = FileOverFileMode(required)
	return strategy
}

func (p *Program) clobberFileOverFile(op *MergeOperation, src, dest *FileNode, targetPath string, strategy FileOverFileStrategy, simFS *FileSystem, ops *[]MergeOperation) {
	// Check if same file
	if src.Path == dest.Path {
		op.Action = "skip"
		return
	}
	srcInfo, err1 := src.GetInfo()
	destInfo, err2 := dest.GetInfo()
	if err1 == nil && err2 == nil && os.SameFile(srcInfo, destInfo) {
		op.Action = "skip"
		return
	}

	// Check if destination is empty or a symlink
	destSize, _ := dest.GetSize()
	if (destSize == 0 || dest.IsSymlink) && !src.IsSymlink {
		op.DeleteDest = true
		return
	}

	// Process optional conditions
	for _, opt := range strategy.Optionals {
		if src.IsSymlink || dest.IsSymlink {
			continue // Skip hashing/size checks for symlinks
		}
		shouldAct := false

		switch opt {
		case SkipHash, DeleteDestHash, DeleteSrcHash:
			match, err := p.compareFiles(src, dest)
			if err != nil {
				continue
			}
			shouldAct = match

		case SkipSize, DeleteDestSize, DeleteSrcSize:
			srcSize, _ := src.GetSize()
			dstSize, _ := dest.GetSize()
			shouldAct = srcSize == dstSize

		case SkipLarger, DeleteDestLarger, DeleteSrcLarger:
			srcSize, _ := src.GetSize()
			dstSize, _ := dest.GetSize()
			shouldAct = srcSize > dstSize

		case SkipSmaller, DeleteDestSmaller, DeleteSrcSmaller:
			srcSize, _ := src.GetSize()
			dstSize, _ := dest.GetSize()
			shouldAct = srcSize < dstSize
		}

		if shouldAct {
			switch opt {
			case SkipHash, SkipSize, SkipLarger, SkipSmaller:
				op.Action = "skip"
				return
			case DeleteDestHash, DeleteDestSize, DeleteDestLarger, DeleteDestSmaller:
				op.DeleteDest = true
				return
			case DeleteSrcHash, DeleteSrcSize, DeleteSrcLarger, DeleteSrcSmaller:
				op.Action = "skip"
				op.DeleteSrc = true
				return
			}
		}

	}

	// Apply required fallback
	switch strategy.Required {
	case FFSkip:
		op.Action = "skip"
	case FFDeleteSrc:
		op.Action = "skip"
		op.DeleteSrc = true
	case FFDeleteDest:
		op.DeleteDest = true
	case FFRenameSrc:
		newPath := getUniqueFilename(targetPath, simFS)
		// Keep action as move/copy, just redirect to newPath
		op.RenamedDestPath = newPath
	case FFRenameDest:
		// destination needs to be renamed first
		newPath := getUniqueFilename(targetPath, simFS)
		// Emit rename for destination, then proceed with normal move/copy
		*ops = append(*ops, MergeOperation{
			SrcPath:  op.DestPath,
			DestPath: newPath,
			Action:   "rename",
			IsDir:    dest.IsDir,
		})
		simFS.Delete(op.DestPath)
		simFS.Add(newPath, dest.Clone(newPath))
		// Keep action as move/copy to original DestPath (now free)
	default:
		op.Action = "skip"
	}
}

func (p *Program) clobber(op *MergeOperation, src, dest *FileNode, targetPath string, mode ConflictMode, simFS *FileSystem, ops *[]MergeOperation) {
	switch mode {
	case CSkip:
		op.Action = "skip"
	case CDeleteSrc:
		op.Action = "skip"
		op.DeleteSrc = true
	case CDeleteDest:
		op.DeleteDest = true
	case CRenameSrc:
		newPath := getUniqueFilename(targetPath, simFS)
		// Keep action as move/copy, just redirect to newPath
		op.RenamedDestPath = newPath
	case CRenameDest:
		newPath := getUniqueFilename(targetPath, simFS)
		// Emit rename for destination
		*ops = append(*ops, MergeOperation{
			SrcPath:  op.DestPath,
			DestPath: newPath,
			Action:   "rename",
			IsDir:    dest.IsDir,
		})
		simFS.Delete(op.DestPath)
		simFS.Add(newPath, dest.Clone(newPath))
		// Keep action as move/copy to original DestPath (now free)
	case CMerge:
		if src.IsDir && !dest.IsDir {
			// Folder over File - Merge mode requires the file to be moved out of the way
			newPath := getUniqueFilename(targetPath, simFS)
			// Emit rename for destination
			*ops = append(*ops, MergeOperation{
				SrcPath:  op.DestPath,
				DestPath: newPath,
				Action:   "rename",
				IsDir:    dest.IsDir,
			})
			simFS.Delete(op.DestPath)
			simFS.Add(newPath, dest.Clone(newPath))
			// Keep action as move/copy to original DestPath (now free)
		} else {
			// Move into the conflicting folder/file
			baseName := filepath.Base(src.Path)
			newPath := filepath.Join(targetPath, baseName)
			// Keep action as move/copy, redirect to newPath inside the directory
			op.RenamedDestPath = newPath
		}
	default:
		op.Action = "skip"
	}
}

func (p *Program) processSource(srcRoot string, srcFS *FileSystem, destFS *FileSystem) error {
	pathChan := p.streamScan(srcRoot, srcFS)

	// Worker pool setup
	numWorkers := p.cli.Workers
	if numWorkers < 1 {
		numWorkers = 1
	}
	jobChan := make(chan MergeJob, numWorkers*2)
	errChan := make(chan error, 128)
	var wg sync.WaitGroup

	// Start workers
	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for job := range jobChan {
				for _, op := range job.Ops {
					if err := p.executeOperation(op, job.Root); err != nil {
						atomic.AddInt64(&p.stats.Errors, 1)
						select {
						case errChan <- fmt.Errorf("%s: %w", op.SrcPath, err):
						default:
							if p.cli.Verbose > 1 {
								fmt.Fprintf(os.Stderr, "\nError (buffer full): %s: %v\n", op.SrcPath, err)
							}
						}

						fmt.Fprintf(os.Stderr, "\nError in job: skipping remaining ops:\n")
						for _, op := range job.Ops {
							fmt.Fprintf(os.Stderr, "  %v: %s\n", op.Action, op.SrcPath)
						}
						break
					}
				}
			}
		}()
	}

	// Planner (runs in main routine or single goroutine to maintain state)
	simFS := NewFileSystem()
	// Copy existing destination into simulation
	destFS.mu.RLock()
	for path, node := range destFS.nodes {
		simFS.Add(path, node.Clone(node.Path))
	}
	for path := range destFS.checked {
		simFS.checked[path] = true
	}
	destFS.mu.RUnlock()

	fileStrategy := parseFileOverFile(p.cli.FileOverFile)
	skipPrefix := ""

	maxBytes := int64(0)
	if p.cli.SizeLimit != "" {
		maxBytes = humanToBytes(p.cli.SizeLimit)
	}

	sourceHasSlash := strings.HasSuffix(srcRoot, string(filepath.Separator)) || strings.HasSuffix(srcRoot, "/")
	relRoot := srcRoot
	if p.cli.RelativeTo != "" {
		relRoot = p.cli.RelativeTo
	}
	relRoot, err := filepath.Abs(relRoot)
	if err != nil {
		close(jobChan)
		return err
	}

	destRoot := p.cli.Destination
	isSourceDir := false
	if info, err := os.Stat(srcRoot); err == nil && info.IsDir() {
		isSourceDir = true
	}

	if p.cli.RelativeTo == "" {
		if isSourceDir {
			if p.cli.Parent || (p.cli.BSD && !sourceHasSlash) {
				destRoot = filepath.Join(destRoot, filepath.Base(srcRoot))
			}
		} else {
			if p.cli.Parent {
				destRoot = filepath.Join(destRoot, filepath.Base(filepath.Dir(srcRoot)))
			}
			appendBasename := true
			if p.cli.DestFile {
				appendBasename = false
			} else if p.cli.DestFolder {
				appendBasename = true
			} else { // DestBSD
				destExistsAsDir := false
				if destNode, ok := destFS.Get(p.cli.Destination); ok && destNode.IsDir {
					destExistsAsDir = true
				} else {
					// Fallback to direct stat if not cached
					if info, err := os.Stat(p.cli.Destination); err == nil && info.IsDir() {
						destExistsAsDir = true
					}
				}

				if strings.HasSuffix(p.cli.Destination, string(filepath.Separator)) || strings.HasSuffix(p.cli.Destination, "/") || destExistsAsDir {
					appendBasename = true
				} else {
					destBase := filepath.Base(p.cli.Destination)
					srcBase := filepath.Base(srcRoot)
					if destBase == srcBase {
						appendBasename = false
					} else {
						existsAsFile := false
						if destNode, ok := destFS.Get(p.cli.Destination); ok && !destNode.IsDir {
							existsAsFile = true
						} else {
							// Fallback to direct stat
							if info, err := os.Stat(p.cli.Destination); err == nil && !info.IsDir() {
								existsAsFile = true
							}
						}
						if existsAsFile {
							appendBasename = false
						} else {
							appendBasename = true
						}
					}
				}
			}
			if appendBasename {
				destRoot = filepath.Join(destRoot, filepath.Base(srcRoot))
			}
		}
	}

	// Capture initial stats before processing this source
	initialFiles := atomic.LoadInt64(&p.stats.FilesProcessed)
	initialFolders := atomic.LoadInt64(&p.stats.FoldersProcessed)
	initialBytes := atomic.LoadInt64(&p.stats.BytesMoved)

	var scheduledFiles, scheduledFolders, scheduledBytes int64
loop:
	for {
		var srcPath string
		var ok bool
		select {
		case <-p.sigChan:
			if p.cli.Resume != "" {
				fmt.Fprintf(os.Stderr, "\nInterrupt received. Saving remaining files...\n")
				p.saveRemaining(srcRoot, pathChan)
			}
			os.Exit(130)
		case srcPath, ok = <-pathChan:
			if !ok {
				break loop
			}
		}

		currentCount := int(initialFiles + initialFolders + scheduledFiles + scheduledFolders)
		currentBytes := initialBytes + scheduledBytes

		if p.cli.Limit > 0 && currentCount >= p.cli.Limit {
			break
		}
		if maxBytes > 0 && currentBytes >= maxBytes {
			break
		}
		if skipPrefix != "" {
			cleanSrc := filepath.Clean(srcPath)
			if strings.HasPrefix(cleanSrc, skipPrefix) {
				continue
			}
		}

		srcNode, _ := srcFS.GetOrLoad(srcPath)

		if !srcNode.IsDir {
			if !p.shouldInclude(srcPath, srcNode) {
				continue
			}
		}

		absSrcPath, err := filepath.Abs(srcPath)
		if err != nil {
			absSrcPath = srcPath
		}

		relPath, err := filepath.Rel(relRoot, absSrcPath)
		if err != nil || strings.HasPrefix(relPath, "..") {
			if p.cli.RelativeTo != "" {
				continue
			}
			relPath = filepath.Base(srcPath)
		}

		destPath := ""
		if !isSourceDir && p.cli.RelativeTo == "" {
			destPath = destRoot
		} else {
			destPath = filepath.Join(destRoot, relPath)
		}

		// Update progress with current file
		if p.cli.Verbose > 0 && !srcNode.IsDir {
			p.updateCurrentFile(relPath)
		}

		op := MergeOperation{
			SrcPath:  srcPath,
			DestPath: destPath,
			IsDir:    srcNode.IsDir,
			SrcNode:  srcNode,
			SrcFS:    srcFS,
		}

		var jobOps []MergeOperation

		hasFilters := len(p.cli.Ext) > 0 || len(p.cli.Include) > 0 || len(p.cli.Exclude) > 0 || len(p.cli.Size) > 0 || p.cli.Limit > 0 || maxBytes > 0

		destNode, exists := simFS.GetOrLoad(destPath)
		if !exists && srcNode.IsDir && (hasFilters || p.cli.Limit > 0 || maxBytes > 0) {
			exists = true
			destNode = &FileNode{IsDir: true}
		}

		if exists {
			atomic.AddInt64(&p.stats.Conflicts, 1)

			if srcNode.IsDir && destNode.IsDir {
				// Folder over folder
				op.Action = "merge"
			} else if !srcNode.IsDir && !destNode.IsDir {
				// File over file
				op.Action = "transfer"
				p.clobberFileOverFile(&op, srcNode, destNode, destPath, fileStrategy, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if !op.DeleteSrc && op.Action != "skip" {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			} else if !srcNode.IsDir && destNode.IsDir {
				// File over folder
				op.Action = "transfer"
				mode := ConflictMode(p.cli.FileOverFolder)
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if !op.DeleteSrc && op.Action != "skip" {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			} else {
				// Folder over file
				op.Action = "transfer"
				mode := ConflictMode(p.cli.FolderOverFile)
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if !op.DeleteSrc && op.Action != "skip" {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			}

		} else {
			op.Action = "transfer"
			simFS.Add(destPath, srcNode.Clone(destPath))
		}

		if op.Action != "merge" && op.Action != "skip" || op.DeleteSrc || op.DeleteDest {
			jobOps = append(jobOps, op)

			// Send job
			jobChan <- MergeJob{Ops: jobOps, Root: destRoot}

			if !op.IsDir {
				sz, _ := srcNode.GetSize()
				scheduledBytes += sz
				scheduledFiles++
			} else {
				scheduledFolders++
			}

			if (op.Action == "transfer" || op.Action == "rename" || op.DeleteSrc) && op.IsDir {
				skipPrefix = filepath.Clean(srcPath) + string(filepath.Separator)
			}
		}
	}

	close(jobChan)
	wg.Wait()

	// Clear progress line if verbose
	if p.cli.Verbose > 0 {
		fmt.Fprint(os.Stderr, "\r\033[K")
	}

	close(errChan)

	var errs []error
	for err := range errChan {
		errs = append(errs, err)
		if p.cli.Verbose > 0 {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
	}

	if len(errs) > 0 {
		return fmt.Errorf("encountered %d errors during phase", len(errs))
	}

	// destFS is passed as pointer, but we made a new simFS. We need to sync back.
	destFS.mu.Lock()
	destFS.checked = simFS.checked
	destFS.nodes = simFS.nodes
	destFS.mu.Unlock()

	return nil
}

func (p *Program) executeOperation(op MergeOperation, root string) error {
	finalDest := op.DestPath
	if op.RenamedDestPath != "" {
		finalDest = op.RenamedDestPath
	}

	if p.cli.Verbose > 0 {
		p.logOp(op, root)
	}

	if p.cli.Simulate {
		return nil
	}

	if op.DeleteDest {
		if err := os.RemoveAll(op.DestPath); err != nil {
			return fmt.Errorf("delete dest: %w", err)
		}
	}

	if op.DeleteSrc {
		if err := os.RemoveAll(op.SrcPath); err != nil {
			return fmt.Errorf("delete src: %w", err)
		}
		return nil
	}

	if op.Action == "skip" {
		return nil
	}

	if err := os.MkdirAll(filepath.Dir(finalDest), 0o755); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}

	isMove := false
	switch op.Action {
	case "transfer":
		isMove = !p.cli.Copy
	case "rename", "delete-dest":
		isMove = true
	}

	// Fallback to simpler node if missing (e.g. usage in tests or renames)
	node := op.SrcNode
	if node == nil {
		// Try to find in SrcFS if available, though for rename-dest SrcFS might not be relevant
		// Just create a temporary node wrapper that will lazy load
		node = &FileNode{Path: op.SrcPath}
	}

	if err := p.performTransfer(op.SrcPath, finalDest, node, isMove, op.SrcFS); err != nil {
		return fmt.Errorf("%s: %w", op.Action, err)
	}

	return nil
}

func (p *Program) performTransfer(srcPath, dstPath string, node *FileNode, isMove bool, fs *FileSystem) error {
	// Try rename first if moving
	if isMove {
		if err := os.Rename(srcPath, dstPath); err == nil {
			// Success
			if node != nil && node.IsDir {
				atomic.AddInt64(&p.stats.FoldersProcessed, 1)
			} else {
				atomic.AddInt64(&p.stats.FilesProcessed, 1)
			}
			return nil
		}
		// Fallback to copy+delete
	}

	// Copy logic (or fallback for move)
	info, err := node.GetInfo()
	if err != nil {
		return err
	}

	// Handle Symlink
	if info.Mode()&os.ModeSymlink != 0 {
		target, err := os.Readlink(srcPath)
		if err != nil {
			return err
		}
		if err := os.Symlink(target, dstPath); err != nil {
			return err
		}
		atomic.AddInt64(&p.stats.FilesProcessed, 1)

		if isMove {
			return os.Remove(srcPath)
		}
		return nil
	}

	// Handle Directory
	if info.IsDir() {
		if err := os.MkdirAll(dstPath, info.Mode()); err != nil {
			return err
		}

		entries, err := os.ReadDir(srcPath)
		if err != nil {
			return err
		}

		for _, entry := range entries {
			childSrc := filepath.Join(srcPath, entry.Name())
			childDst := filepath.Join(dstPath, entry.Name())

			// Try to find cached node to avoid Lstat
			var childNode *FileNode
			if fs != nil {
				childNode, _ = fs.Get(childSrc)
			}
			if childNode == nil {
				childNode = &FileNode{Path: childSrc}
			}

			if err := p.performTransfer(childSrc, childDst, childNode, isMove, fs); err != nil {
				return err
			}
		}
		atomic.AddInt64(&p.stats.FoldersProcessed, 1)

		if isMove {
			return os.Remove(srcPath)
		}
		return nil
	}

	// Handle Regular File
	if err := copyFile(srcPath, dstPath); err != nil {
		return err
	}

	size, _ := node.GetSize()
	atomic.AddInt64(&p.stats.BytesMoved, size)
	atomic.AddInt64(&p.stats.FilesProcessed, 1)

	if isMove {
		return os.Remove(srcPath)
	}
	return nil
}

func (p *Program) shouldInclude(path string, node *FileNode) bool {
	name := filepath.Base(path)
	if len(p.cli.Ext) > 0 {
		match := false
		for _, ext := range p.cli.Ext {
			if strings.HasSuffix(name, ext) {
				match = true
				break
			}
		}
		if !match {
			return false
		}
	}

	if len(p.cli.Include) > 0 {
		match := false
		for _, pattern := range p.cli.Include {
			if matched, _ := filepath.Match(pattern, name); matched {
				match = true
				break
			}
		}
		if !match {
			return false
		}
	}

	if len(p.cli.Exclude) > 0 {
		for _, pattern := range p.cli.Exclude {
			if matched, _ := filepath.Match(pattern, name); matched {
				return false
			}
		}
	}

	// Check size constraints using cached GetInfo
	if len(p.cli.Size) > 0 {
		size, err := node.GetSize()
		if err != nil {
			return false
		}
		if !p.sizeFilter(size) {
			return false
		}
	}

	return true
}

func removeEmptyDirs(root string) error {
	var dirs []string
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			dirs = append(dirs, path)
		}
		return nil
	})
	if err != nil {
		return err
	}

	for i := len(dirs) - 1; i >= 0; i-- {
		entries, err := os.ReadDir(dirs[i])
		if err != nil {
			continue
		}
		if len(entries) == 0 {
			_ = os.Remove(dirs[i])
		}
	}

	return nil
}

func main() {
	cli := &CLI{}
	kong.Parse(cli,
		kong.Name("merge"),
		kong.Description("Merge folders with apriori conflict resolution"),
		kong.UsageOnError(),
	)

	p := NewProgram(cli)

	// Scan destination, add it to destFS so conflicts are detected
	destFS := NewFileSystem()
	destFS.GetOrLoad(cli.Destination)

	// Process each source
	for _, src := range cli.Sources {
		if _, err := os.Stat(src); err != nil {
			fmt.Fprintf(os.Stderr, "Source %s does not exist", src)
			continue
		}

		srcFS := NewFileSystem()
		// Stream parallel processing
		err := p.processSource(src, srcFS, destFS)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error processing source %s: %v", src, err)
		}

		// Clean up empty directories
		if !cli.Copy && !cli.Simulate {
			removeEmptyDirs(src)
		}
	}

	if cli.Verbose > 0 {
		p.stats.Print()
	}
}

func (p *Program) logOp(op MergeOperation, root string) {
	finalDest := op.DestPath
	if op.RenamedDestPath != "" {
		finalDest = op.RenamedDestPath
	}

	rel := finalDest
	if root != "" {
		if r, err := filepath.Rel(root, finalDest); err == nil {
			rel = r
		}
	}

	action := op.Action
	if op.DeleteDest {
		action = "replace"
	}

	fmt.Fprintf(os.Stderr, "\n%-10s %s", action, rel)
}
