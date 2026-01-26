package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/alecthomas/kong"
)

// Conflict resolution modes
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

	info       os.FileInfo // Cached file info
	infoLoaded bool
	mu         sync.Mutex
	sampleHash string // Cached sample hash
	fullHash   string // Cached full hash
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
		Path:  newPath,
		IsDir: n.IsDir,

		IsSymlink:  n.IsSymlink,
		info:       n.info,
		infoLoaded: n.infoLoaded,
		sampleHash: n.sampleHash,
		fullHash:   n.fullHash,
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
		Path:       path, // We use the requested path
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
	Simulate bool `help:"Simulate without making changes" alias:"dry-run" short:"n"`
	Workers  int  `help:"Number of parallel workers" default:"4" alias:"threads" short:"j"`
	Verbose  int  `help:"Verbose output (0-2)" short:"v" type:"counter"`

	Ext       []string `help:"Filter by file extensions" short:"e"`
	Exclude   []string `help:"Exclude patterns" short:"E"`
	Include   []string `help:"Include patterns" short:"I"`
	Limit     int      `help:"Limit number of files transferred" short:"l"`
	SizeLimit string   `help:"Limit total size of files transferred (e.g., 100M, 1G)" short:"sl"`

	RelativeTo string `help:"Preserve directory hierarchy relative to path"`
	Relative   bool   `help:"Shortcut for --relative-to=/"`

	Parent bool `help:"Include parent folder name" short:"P"`
	BSD    bool `help:"rsync/BSD mv behavior (src trailing slash matters)"`

	DestBSD    bool `help:"BSD destination mode (default)"`
	DestFolder bool `help:"Destination is always a folder" alias:"folder" short:"t"`
	DestFile   bool `help:"Destination is a file (no-target-directory)" alias:"file" short:"T"`
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

type Program struct {
	cli   *CLI
	stats Stats
}

func NewProgram(cli *CLI) *Program {
	return &Program{cli: cli}
}

// sampleHash computes a hash from samples across the file for quick comparison.
// It returns the hash string, a boolean indicating if it's a full hash, and any error.
func sampleHash(path string, gap float64) (string, bool, error) {
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

// computeFullHash computes SHA-256 of entire file
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

// compareFiles does a two-stage comparison: sample hash then full hash
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

func scanDirectory(root string, fs *FileSystem) ([]string, error) {
	var paths []string
	err := filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
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

		paths = append(paths, path)
		return nil
	})
	return paths, err
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
		newPath := getUniqueFilename(targetPath, simFS)
		// Emit rename for destination, then proceed with normal move/copy
		*ops = append(*ops, MergeOperation{
			SrcPath:  op.DestPath,
			DestPath: newPath,
			Action:   "rename",
			IsDir:    dest.IsDir,
		})
		simFS.Delete(op.DestPath)
		dest.Path = newPath // Update the node's internal path
		simFS.Add(newPath, dest)
		// Keep action as move/copy to original DestPath (now cleared)
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
		dest.Path = newPath // Update the node's internal path
		simFS.Add(newPath, dest)
		// Keep action as move/copy to original DestPath (now cleared)
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
			dest.Path = newPath // Update the node's internal path
			simFS.Add(newPath, dest)
			// Keep action as move/copy to original DestPath (now cleared)
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

func (p *Program) planMerge(srcRoot string, srcFS *FileSystem, srcPaths []string, destFS *FileSystem) ([]MergeOperation, *FileSystem, error) {
	var ops []MergeOperation
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
	var err error
	relRoot, err = filepath.Abs(relRoot)
	if err != nil {
		return nil, nil, err
	}

	// Determine destination root for this source
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
			// Source is a file
			if p.cli.Parent {
				destRoot = filepath.Join(destRoot, filepath.Base(filepath.Dir(srcRoot)))
			}

			appendBasename := true
			if p.cli.DestFile {
				appendBasename = false
			} else if p.cli.DestFolder {
				appendBasename = true
			} else { // DestBSD (default)
				destExistsAsDir := false
				if destNode, ok := destFS.Get(p.cli.Destination); ok && destNode.IsDir {
					destExistsAsDir = true
				} else {
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
						if info, err := os.Stat(p.cli.Destination); err == nil && !info.IsDir() {
							existsAsFile = true
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

	plannedCount := int(atomic.LoadInt64(&p.stats.FilesProcessed) + atomic.LoadInt64(&p.stats.FoldersProcessed))
	plannedBytes := atomic.LoadInt64(&p.stats.BytesMoved)

	for _, srcPath := range srcPaths {
		if p.cli.Limit > 0 && plannedCount >= p.cli.Limit {
			break
		}
		if maxBytes > 0 && plannedBytes >= maxBytes {
			break
		}
		if skipPrefix != "" && strings.HasPrefix(srcPath, skipPrefix) {
			continue
		}

		srcNode, _ := srcFS.Get(srcPath)

		// Filter by expressions
		if !srcNode.IsDir {
			if !p.shouldInclude(srcPath) {
				continue
			}
		}

		// Calculate relative path
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

		op := MergeOperation{
			SrcPath:  srcPath,
			DestPath: destPath,
			IsDir:    srcNode.IsDir,
			SrcNode:  srcNode,
			SrcFS:    srcFS,
		}

		hasFilters := len(p.cli.Ext) > 0 || len(p.cli.Include) > 0 || len(p.cli.Exclude) > 0 || p.cli.Limit > 0 || maxBytes > 0

		// Check for conflicts
		destNode, exists := simFS.GetOrLoad(destPath)
		if !exists && srcNode.IsDir && (hasFilters || p.cli.Limit > 0 || maxBytes > 0) {
			// Force merge mode for directories if filters or limits are present to ensure recursion
			exists = true
			destNode = &FileNode{IsDir: true}
		}

		if exists {
			atomic.AddInt64(&p.stats.Conflicts, 1)

			if srcNode.IsDir && destNode.IsDir {
				// Folder over folder - typically merge
				op.Action = "merge"
			} else if !srcNode.IsDir && !destNode.IsDir {
				// File over file
				op.Action = "transfer"
				p.clobberFileOverFile(&op, srcNode, destNode, destPath, fileStrategy, simFS, &ops)
				// Apply simulation updates
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
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &ops)
				// Apply simulation updates
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
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &ops)
				// Apply simulation updates
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
			// No conflict
			op.Action = "transfer"
			simFS.Add(destPath, srcNode.Clone(destPath))
		}

		if op.Action != "merge" && op.Action != "skip" || op.DeleteSrc || op.DeleteDest {
			ops = append(ops, op)
			plannedCount++
			if !op.IsDir {
				sz, _ := srcNode.GetSize()
				plannedBytes += sz
			}
			// If we are moving/copying a directory as a whole, skip its children
			if (op.Action == "transfer" || op.Action == "rename" || op.DeleteSrc) && op.IsDir {
				skipPrefix = srcPath + string(filepath.Separator)
				// Add children to simFS so subsequent merges know they exist
				finalDest := op.DestPath
				if op.RenamedDestPath != "" {
					finalDest = op.RenamedDestPath
				}
				srcFS.mu.RLock()
				for p, node := range srcFS.nodes {
					if strings.HasPrefix(p, skipPrefix) {
						rel, _ := filepath.Rel(srcPath, p)
						childDest := filepath.Join(finalDest, rel)
						simFS.Add(childDest, node.Clone(childDest))
					}
				}
				srcFS.mu.RUnlock()
			}
		}
	}

	return ops, simFS, nil
}

func (p *Program) executeOperation(op MergeOperation) error {
	finalDest := op.DestPath
	if op.RenamedDestPath != "" {
		finalDest = op.RenamedDestPath
	}

	if p.cli.Verbose > 0 {
		action := op.Action
		if op.DeleteDest {
			action = "replace"
		}
		fmt.Printf("%s: %s -> %s\n", action, op.SrcPath, finalDest)
	}

	if p.cli.Simulate {
		return nil
	}

	// Delete destination if needed
	if op.DeleteDest {
		if err := os.RemoveAll(op.DestPath); err != nil {
			return fmt.Errorf("delete dest: %w", err)
		}
	}

	// Delete source if needed
	if op.DeleteSrc {
		if err := os.RemoveAll(op.SrcPath); err != nil {
			return fmt.Errorf("delete src: %w", err)
		}
		return nil
	}

	// Skip operation
	if op.Action == "skip" {
		return nil
	}

	// Create parent directory
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
	src, err := os.Open(srcPath)
	if err != nil {
		return err
	}
	defer src.Close()

	dst, err := os.OpenFile(dstPath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, info.Mode())
	if err != nil {
		return err
	}
	defer dst.Close()

	n, err := io.Copy(dst, src)
	if err != nil {
		return err
	}
	atomic.AddInt64(&p.stats.BytesMoved, n)
	atomic.AddInt64(&p.stats.FilesProcessed, 1)

	if isMove {
		return os.Remove(srcPath)
	}
	return nil
}

func isInside(path, parent string) bool {
	absPath, err1 := filepath.Abs(path)
	absParent, err2 := filepath.Abs(parent)
	if err1 != nil || err2 != nil {
		return strings.HasPrefix(filepath.Clean(path), filepath.Clean(parent)+string(filepath.Separator))
	}
	return strings.HasPrefix(filepath.Clean(absPath), filepath.Clean(absParent)+string(filepath.Separator))
}

func (p *Program) executeOperations(ops []MergeOperation) error {
	// Plan: Renames of existing files must happen before moves into their places.
	// Since rename-dest operations move something FROM the destination,
	// we execute them in the first phase.
	var phase1 []MergeOperation // Renames/Preparations
	var phase2 []MergeOperation // Moves/Copies

	absDest, _ := filepath.Abs(p.cli.Destination)

	for _, op := range ops {
		// If the source is already in the destination folder, it's likely a rename-dest
		if isInside(op.SrcPath, absDest) {
			phase1 = append(phase1, op)
		} else {
			phase2 = append(phase2, op)
		}
	}

	if err := p.runOperationPhase(phase1); err != nil {
		return err
	}
	return p.runOperationPhase(phase2)
}

func (p *Program) runOperationPhase(ops []MergeOperation) error {
	if len(ops) == 0 {
		return nil
	}

	numWorkers := p.cli.Workers
	if numWorkers < 1 {
		numWorkers = 1
	}

	opChanSize := len(ops)
	if opChanSize > 4096 {
		opChanSize = 4096
	}
	opChan := make(chan MergeOperation, opChanSize)
	errChan := make(chan error, 128) // Small buffer for errors
	var wg sync.WaitGroup

	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for op := range opChan {
				if err := p.executeOperation(op); err != nil {
					atomic.AddInt64(&p.stats.Errors, 1)
					select {
					case errChan <- fmt.Errorf("%s: %w", op.SrcPath, err):
					default:
						// Buffer full, drop or print
						if p.cli.Verbose > 1 {
							fmt.Fprintf(os.Stderr, "Error (buffer full): %s: %v\n", op.SrcPath, err)
						}
					}
				}
			}
		}()
	}

	for _, op := range ops {
		opChan <- op
	}
	close(opChan)
	wg.Wait()
	close(errChan)

	var errs []error
	for err := range errChan {
		errs = append(errs, err)
		if p.cli.Verbose > 1 {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
	}

	if len(errs) > 0 {
		return fmt.Errorf("encountered %d errors during phase", len(errs))
	}
	return nil
}

func (p *Program) shouldInclude(path string) bool {
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

	return true
}

func removeEmptyDirs(path string) error {
	entries, err := os.ReadDir(path)
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if entry.IsDir() {
			if err := removeEmptyDirs(filepath.Join(path, entry.Name())); err != nil {
				return err
			}
		}
	}
	// Re-read entries
	entries, err = os.ReadDir(path)
	if err != nil {
		return err
	}
	if len(entries) == 0 {
		return os.Remove(path)
	}
	return nil
}

func main() {
	cli := &CLI{}
	ctx := kong.Parse(cli,
		kong.Name("merge"),
		kong.Description("Merge folders with sophisticated conflict resolution"),
		kong.UsageOnError(),
	)

	p := NewProgram(cli)

	// Scan destination
	destFS := NewFileSystem()
	if info, err := os.Stat(cli.Destination); err == nil {
		if info.IsDir() {
			// It's a directory, we do not scan it. Lazy loading will handle conflict checks.
		} else {
			// It's a file, add it to destFS so conflicts are detected
			destFS.Add(cli.Destination, &FileNode{
				Path:       cli.Destination,
				IsDir:      false,
				info:       info,
				infoLoaded: true,
			})
		}
	}

	// Process each source
	for _, src := range cli.Sources {
		srcFS := NewFileSystem()
		srcPaths, err := scanDirectory(src, srcFS)
		if err != nil {
			ctx.Fatalf("Error scanning source %s: %v", src, err)
		}

		ops, simFS, err := p.planMerge(src, srcFS, srcPaths, destFS)
		if err != nil {
			ctx.Fatalf("Error planning merge: %v", err)
		}

		if cli.Verbose > 0 {
			fmt.Printf("Source: %s\n", src)
			fmt.Printf("  Operations: %d\n", len(ops))
			fmt.Printf("  Conflicts: %d\n", p.stats.Conflicts)
		}

		if err := p.executeOperations(ops); err != nil {
			ctx.Fatalf("Error executing operations: %v", err)
		}

		// Update destFS with simFS for next source
		destFS = simFS

		// Clean up empty directories
		if !cli.Copy && !cli.Simulate {
			removeEmptyDirs(src)
		}
	}

	if cli.Verbose > 0 {
		p.stats.Print()
	}
}
