package main

import (
	"bufio"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/alecthomas/kong"
)

type Program struct {
	cli        *CLI
	stats      Stats
	progress   Progress
	sigChan    chan os.Signal
	sizeFilter func(int64) bool
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

type MergeJob struct {
	Ops  []MergeOperation
	Root string
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
			p.progress.currentRel.Store(relPath)

			// Print progress every 200ms to avoid excessive updates
			now := time.Now()
			if now.Sub(p.progress.lastPrintTime) > 200*time.Millisecond {
				p.printProgress()
			}
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
