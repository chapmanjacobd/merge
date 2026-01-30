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
	Copy            bool
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
			fmt.Fprintf(os.Stderr, "Source %s does not exist\n", ShellQuote(src))
			continue
		}

		srcFS := NewFileSystem()
		// Stream parallel processing
		err := p.processSource(src, srcFS, destFS)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error processing source %s: %v\n", ShellQuote(src), err)
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
	// Worker pool setup
	numWorkers := p.cli.Workers
	if numWorkers < 1 {
		numWorkers = 1
	}
	jobChan := make(chan MergeJob) // Unbuffered to ensure scheduler controls dispatch
	doneChan := make(chan MergeJob, numWorkers*2)
	errChan := make(chan error, 128)
	var wg sync.WaitGroup

	// Start workers
	p.logDebug("Starting %d workers", numWorkers)
	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for job := range jobChan {
				for _, op := range job.Ops {
					if err := p.executeOperation(op, job.Root); err != nil {
						atomic.AddInt64(&p.stats.Errors, 1)
						select {
						case errChan <- fmt.Errorf("%s: %v", ShellQuote(op.SrcPath), err):
						default:
							if p.cli.Verbose > 0 {
								p.printLog(fmt.Sprintf("Error (buffer full): %s: %v", ShellQuote(op.SrcPath), err))
							}
						}
						p.printLog(fmt.Sprintf("Error in job: %v", err))
					}
				}
				doneChan <- job
			}
		}()
	}

	// Channel for planned jobs and final simFS
	plannedJobsChan := make(chan MergeJob, 1024)
	simReturnChan := make(chan *FileSystem, 1)

	// Start Planner
	go p.generateJobs(srcRoot, srcFS, destFS, plannedJobsChan, simReturnChan)

	// Scheduler State
	pendingJobs := []MergeJob{}
	activePaths := make(map[string]int)
	activeWorkers := 0
	plannerFinished := false
	var finalSimFS *FileSystem

	// Helper to collect paths from a job
	getJobPaths := func(job MergeJob) []string {
		var paths []string
		seen := make(map[string]bool)
		add := func(p string) {
			if p == "" {
				return
			}
			if !seen[p] {
				seen[p] = true
				paths = append(paths, p)
			}
		}
		for _, op := range job.Ops {
			add(op.DestPath)
			add(op.RenamedDestPath)
			add(op.SrcPath)
		}
		return paths
	}

	for {
		// Find first runnable job in pending queue (FIFO priority for dependent jobs)
		var nextJob MergeJob
		nextJobIdx := -1

		// Preserve FIFO for dependent jobs by keeping track of paths touched by preceding blocked jobs
		blockedByPending := make(map[string]bool)
		for p := range activePaths {
			blockedByPending[p] = true
		}

		for i, job := range pendingJobs {
			conflict := false
			paths := getJobPaths(job)
			for _, path := range paths {
				if blockedByPending[path] {
					conflict = true
					break
				}
			}

			if !conflict {
				nextJob = job
				nextJobIdx = i
				break
			}

			// This job is blocked, so ALL its paths are now blocked for subsequent jobs in the queue
			for _, path := range paths {
				blockedByPending[path] = true
			}
		}

		// Prepare send channel if we have a runnable job
		var outChan chan<- MergeJob
		if nextJobIdx != -1 {
			outChan = jobChan
		}

		// Exit condition
		if plannerFinished && len(pendingJobs) == 0 && activeWorkers == 0 {
			break
		}

		// Deadlock Detection
		if plannerFinished && len(pendingJobs) > 0 && activeWorkers == 0 && nextJobIdx == -1 {
			return fmt.Errorf("deadlock detected: %d jobs pending but none runnable and no active workers", len(pendingJobs))
		}

		select {
		case job, ok := <-plannedJobsChan:
			if !ok {
				plannedJobsChan = nil
				plannerFinished = true
			} else {
				pendingJobs = append(pendingJobs, job)
			}

		case simResult := <-simReturnChan:
			finalSimFS = simResult

		case completedJob := <-doneChan:
			paths := getJobPaths(completedJob)
			for _, path := range paths {
				activePaths[path]--
				if activePaths[path] <= 0 {
					delete(activePaths, path)
				}
			}
			activeWorkers--

		case outChan <- nextJob:
			// Job successfully dispatched to worker
			paths := getJobPaths(nextJob)
			for _, path := range paths {
				activePaths[path]++
			}
			activeWorkers++
			// Remove from pending
			pendingJobs = append(pendingJobs[:nextJobIdx], pendingJobs[nextJobIdx+1:]...)

		case <-time.After(1 * time.Second):
			// Safety timeout to avoid spinning too fast if everything is blocked
			// Also allows checking exit conditions periodically
		}
	}

	close(jobChan)
	wg.Wait()

	if p.cli.Verbose > 0 {
		fmt.Fprint(os.Stderr, "\r\033[K")
	}

	// Wait for the simulation result if we don't have it yet
	if finalSimFS == nil && simReturnChan != nil {
		select {
		case simResult := <-simReturnChan:
			finalSimFS = simResult
		case <-time.After(100 * time.Millisecond):
		}
	}

	// Synchronize the simulated state back to destFS for the next source
	if finalSimFS != nil {
		destFS.mu.Lock()
		destFS.nodes = finalSimFS.nodes
		destFS.checked = finalSimFS.checked
		destFS.mu.Unlock()
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

	return nil
}

func (p *Program) generateJobs(srcRoot string, srcFS *FileSystem, destFS *FileSystem, jobChan chan<- MergeJob, simReturn chan<- *FileSystem) {
	defer close(jobChan)

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

	defer func() {
		select {
		case simReturn <- simFS:
		default:
		}
	}()

	fileStrategy := parseFileOverFile(p.cli.FileOverFile)
	isMove := !p.cli.Copy
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
		fmt.Fprintf(os.Stderr, "Error getting absolute path for %s: %v\n", ShellQuote(relRoot), err)
		return
	}

	pathChan := p.streamScan(srcRoot, srcFS)

	destRoot, _ := filepath.Abs(p.cli.Destination)
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
				} else if info, err := os.Stat(p.cli.Destination); err == nil && info.IsDir() {
					destExistsAsDir = true
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
						} else if info, err := os.Stat(p.cli.Destination); err == nil && !info.IsDir() {
							existsAsFile = true
						}
						appendBasename = !existsAsFile
					}
				}
			}
			if appendBasename {
				destRoot = filepath.Join(destRoot, filepath.Base(srcRoot))
			}
		}
	}

	initialFiles := atomic.LoadInt64(&p.stats.FilesMerged)
	initialFolders := atomic.LoadInt64(&p.stats.FoldersMerged)
	initialBytes := atomic.LoadInt64(&p.stats.BytesMoved)

	var scheduledFiles, scheduledFolders, scheduledBytes int64

outerloop:
	for {
		var srcPath string
		var ok bool
		select {
		case <-p.sigChan:
			os.Exit(130)
		case srcPath, ok = <-pathChan:
			if !ok {
				break outerloop
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

		relPath, _ := filepath.Rel(relRoot, absSrcPath)
		if strings.HasPrefix(relPath, "..") {
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

		if p.cli.Verbose > 0 && !srcNode.IsDir {
			p.progress.currentRel.Store(relPath)
			now := time.Now()
			if now.Sub(p.progress.lastPrintTime) > 200*time.Millisecond {
				p.printProgress()
			}
		}

		op := MergeOperation{
			SrcPath:   srcPath,
			DestPath:  destPath,
			IsDir:     srcNode.IsDir,
			SrcNode:   srcNode,
			SrcFS:     srcFS,
			DeleteSrc: false,
		}

		var jobOps []MergeOperation
		hasFilters := len(p.cli.Ext) > 0 || len(p.cli.Include) > 0 || len(p.cli.Exclude) > 0 || len(p.cli.Size) > 0 || p.cli.Limit > 0 || maxBytes > 0

		destNode, exists := simFS.GetOrLoad(destPath)
		if !exists && srcNode.IsDir && (hasFilters || p.cli.Limit > 0 || maxBytes > 0) {
			exists = true
			destNode = &FileNode{IsDir: true}
		}

		if exists {
			if srcNode.IsDir && destNode.IsDir {
				// Folder over folder
			} else if !srcNode.IsDir && !destNode.IsDir {
				atomic.AddInt64(&p.stats.FileOverFile, 1)
				op.Copy = true
				op.DeleteSrc = isMove
				p.clobberFileOverFile(&op, srcNode, destNode, destPath, fileStrategy, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if op.Copy {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			} else if !srcNode.IsDir && destNode.IsDir {
				// File over folder
				atomic.AddInt64(&p.stats.FileOverFolder, 1)
				op.Copy = true
				op.DeleteSrc = isMove
				mode := ConflictMode(p.cli.FileOverFolder)
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if op.Copy {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			} else {
				// Folder over file
				atomic.AddInt64(&p.stats.FolderOverFile, 1)
				op.Copy = true
				op.DeleteSrc = isMove
				mode := ConflictMode(p.cli.FolderOverFile)
				p.clobber(&op, srcNode, destNode, destPath, mode, simFS, &jobOps)
				if op.DeleteDest {
					simFS.Delete(op.DestPath)
				}
				if op.Copy {
					finalPath := op.DestPath
					if op.RenamedDestPath != "" {
						finalPath = op.RenamedDestPath
					}
					simFS.Add(finalPath, srcNode.Clone(finalPath))
				}
			}
		} else {
			op.Copy = true
			op.DeleteSrc = isMove
			simFS.Add(destPath, srcNode.Clone(destPath))
		}

		if op.Copy || op.DeleteSrc || op.DeleteDest {
			jobOps = append(jobOps, op)
			jobChan <- MergeJob{Ops: jobOps, Root: destRoot}

			if !op.IsDir {
				sz, _ := srcNode.GetSize()
				scheduledBytes += sz
				scheduledFiles++
			} else {
				scheduledFolders++
			}

			if (op.Copy || op.DeleteSrc) && op.IsDir {
				skipPrefix = filepath.Clean(srcPath) + string(filepath.Separator)
			}
		}
	}
}

func (p *Program) executeOperation(op MergeOperation, root string) error {
	finalDest := op.DestPath
	if op.RenamedDestPath != "" {
		finalDest = op.RenamedDestPath
	}

	node := op.SrcNode
	if node == nil {
		node = &FileNode{Path: op.SrcPath}
	}

	if p.cli.Verbose > 0 || p.cli.Simulate {
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

	if op.DeleteSrc && !op.Copy {
		if err := os.RemoveAll(op.SrcPath); err != nil {
			return fmt.Errorf("delete src %s: %w", ShellQuote(op.SrcPath), err)
		}
		return nil
	}

	if !op.Copy {
		return nil
	}

	if err := os.MkdirAll(filepath.Dir(finalDest), 0o755); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}

	if err := p.performTransfer(op.SrcPath, finalDest, node, op.DeleteSrc, op.SrcFS); err != nil {
		return fmt.Errorf("transfer %s -> %s: %w", ShellQuote(op.SrcPath), ShellQuote(finalDest), err)
	}

	return nil
}

func (p *Program) performTransfer(srcPath, dstPath string, node *FileNode, isMove bool, fs *FileSystem) error {
	if isMove {
		if err := os.Rename(srcPath, dstPath); err == nil {
			if node != nil && node.IsDir {
				atomic.AddInt64(&p.stats.FoldersMerged, 1)
			} else {
				atomic.AddInt64(&p.stats.FilesMerged, 1)
			}
			return nil
		}
	}

	info, err := node.GetInfo()
	if err != nil {
		return err
	}

	if info.Mode()&os.ModeSymlink != 0 {
		target, _ := os.Readlink(srcPath)
		if err := os.Symlink(target, dstPath); err != nil {
			return err
		}
		atomic.AddInt64(&p.stats.FilesMerged, 1)
		if isMove {
			return os.Remove(srcPath)
		}
		return nil
	}

	if info.IsDir() {
		if err := os.MkdirAll(dstPath, info.Mode().Perm()); err != nil {
			return err
		}
		entries, _ := os.ReadDir(srcPath)
		var errs []error
		for _, entry := range entries {
			childSrc := filepath.Join(srcPath, entry.Name())
			childDst := filepath.Join(dstPath, entry.Name())
			var childNode *FileNode
			if fs != nil {
				childNode, _ = fs.Get(childSrc)
			}
			if childNode == nil {
				childNode = &FileNode{Path: childSrc}
			}
			if err := p.performTransfer(childSrc, childDst, childNode, isMove, fs); err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				errs = append(errs, err)
				continue
			}
		}
		atomic.AddInt64(&p.stats.FoldersMerged, 1)
		if isMove {
			if len(errs) > 0 {
				return fmt.Errorf("failed to move directory %s: %v", ShellQuote(srcPath), errs)
			}
			return os.RemoveAll(srcPath)
		}
		return nil
	}

	if !info.Mode().IsRegular() {
		p.logDebug("Skipping special file: %s (mode %v)", ShellQuote(srcPath), info.Mode())
		return nil
	}

	if err := copyFile(srcPath, dstPath); err != nil {
		return err
	}

	size, _ := node.GetSize()
	atomic.AddInt64(&p.stats.BytesMoved, size)
	atomic.AddInt64(&p.stats.FilesMerged, 1)

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
		absRoot, _ := filepath.Abs(root)
		destAbs, _ := filepath.Abs(p.cli.Destination)
		filepath.WalkDir(absRoot, func(path string, d os.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() && path == destAbs {
				return filepath.SkipDir
			}

			info, _ := d.Info()

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
