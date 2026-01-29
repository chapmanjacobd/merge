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
)

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

func (p *Program) clobberFileOverFile(op *MergeOperation, src, dest *FileNode, targetPath string, strategy FileOverFileStrategy, simFS *FileSystem, ops *[]MergeOperation) {
	// Check if same file
	if src.Path == dest.Path {
		p.logDebug("Skipping %s (same source and destination path)", ShellQuote(src.Path))
		op.Copy = false
		return
	}
	srcInfo, err1 := src.GetInfo()
	destInfo, err2 := dest.GetInfo()
	if err1 == nil && err2 == nil && os.SameFile(srcInfo, destInfo) {
		p.logDebug("Skipping %s (same inode as destination)", ShellQuote(src.Path))
		op.Copy = false
		return
	}

	// Check if destination is empty or a symlink
	destSize, _ := dest.GetSize()
	if (destSize == 0 || dest.IsSymlink) && !src.IsSymlink {
		p.logDebug("Replacing %s (destination is empty or symlink)", ShellQuote(targetPath))
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
				p.logDebug("Skipping %s (matches optional strategy: %s)", ShellQuote(src.Path), opt)
				op.Copy = false
				op.DeleteSrc = false
				return
			case DeleteDestHash, DeleteDestSize, DeleteDestLarger, DeleteDestSmaller:
				p.logDebug("Replacing %s (matches optional strategy: %s)", ShellQuote(targetPath), opt)
				op.DeleteDest = true
				return
			case DeleteSrcHash, DeleteSrcSize, DeleteSrcLarger, DeleteSrcSmaller:
				p.logDebug("Deleting source %s (matches optional strategy: %s)", ShellQuote(src.Path), opt)
				op.Copy = false
				op.DeleteSrc = true
				return
			}
		}

	}

	// Apply required fallback
	switch strategy.Required {
	case FFSkip:
		p.logDebug("Skipping %s (required strategy: skip)", ShellQuote(src.Path))
		op.Copy = false
		op.DeleteSrc = false
	case FFDeleteSrc:
		p.logDebug("Deleting source %s (required strategy: delete-src)", ShellQuote(src.Path))
		op.Copy = false
		op.DeleteSrc = true
	case FFDeleteDest:
		p.logDebug("Replacing %s (required strategy: delete-dest)", ShellQuote(targetPath))
		op.DeleteDest = true
	case FFRenameSrc:
		newPath := getUniqueFilename(targetPath, simFS)
		p.logDebug("Renaming source %s -> %s (required strategy: rename-src)", ShellQuote(src.Path), ShellQuote(newPath))
		// Keep action as move/copy, just redirect to newPath
		op.RenamedDestPath = newPath
	case FFRenameDest:
		// destination needs to be renamed first
		newPath := getUniqueFilename(targetPath, simFS)
		p.logDebug("Renaming destination %s -> %s (required strategy: rename-dest)", ShellQuote(targetPath), ShellQuote(newPath))
		// Emit rename for destination, then proceed with normal move/copy
		*ops = append(*ops, MergeOperation{
			SrcPath:   op.DestPath,
			DestPath:  newPath,
			Copy:      true,
			DeleteSrc: true,
			IsDir:     dest.IsDir,
		})
		simFS.Delete(op.DestPath)
		simFS.Add(newPath, dest.Clone(newPath))
		// Keep action as move/copy to original DestPath (now free)
	default:
		p.logDebug("Skipping %s (unknown required strategy, defaulting to skip)", ShellQuote(src.Path))
		op.Copy = false
	}
}

func (p *Program) clobber(op *MergeOperation, src, dest *FileNode, targetPath string, mode ConflictMode, simFS *FileSystem, ops *[]MergeOperation) {
	switch mode {
	case CSkip:
		p.logDebug("Skipping %s (conflict strategy: skip)", ShellQuote(src.Path))
		op.Copy = false
		op.DeleteSrc = false
	case CDeleteSrc:
		p.logDebug("Deleting source %s (conflict strategy: delete-src)", ShellQuote(src.Path))
		op.Copy = false
		op.DeleteSrc = true
	case CDeleteDest:
		p.logDebug("Replacing %s (conflict strategy: delete-dest)", ShellQuote(targetPath))
		op.DeleteDest = true
	case CRenameSrc:
		newPath := getUniqueFilename(targetPath, simFS)
		p.logDebug("Renaming source %s -> %s (conflict strategy: rename-src)", ShellQuote(src.Path), ShellQuote(newPath))
		// Keep action as move/copy, just redirect to newPath
		op.RenamedDestPath = newPath
	case CRenameDest:
		newPath := getUniqueFilename(targetPath, simFS)
		p.logDebug("Renaming destination %s -> %s (conflict strategy: rename-dest)", ShellQuote(targetPath), ShellQuote(newPath))
		// Emit rename for destination
		*ops = append(*ops, MergeOperation{
			SrcPath:   op.DestPath,
			DestPath:  newPath,
			Copy:      true,
			DeleteSrc: true,
			IsDir:     dest.IsDir,
		})
		simFS.Delete(op.DestPath)
		simFS.Add(newPath, dest.Clone(newPath))
		// Keep action as move/copy to original DestPath (now free)
	case CMerge:
		if src.IsDir && !dest.IsDir {
			// Folder over File - Merge mode requires the file to be moved out of the way
			newPath := getUniqueFilename(targetPath, simFS)
			p.logDebug("Renaming destination %s -> %s (folder-over-file merge strategy)", ShellQuote(targetPath), ShellQuote(newPath))
			// Emit rename for destination
			*ops = append(*ops, MergeOperation{
				SrcPath:   op.DestPath,
				DestPath:  newPath,
				Copy:      true,
				DeleteSrc: true,
				IsDir:     dest.IsDir,
			})
			simFS.Delete(op.DestPath)
			simFS.Add(newPath, dest.Clone(newPath))
			// Keep action as move/copy to original DestPath (now free)
		} else {
			// Move into the conflicting folder/file
			baseName := filepath.Base(src.Path)
			newPath := filepath.Join(targetPath, baseName)
			p.logDebug("Moving %s -> %s (merge strategy)", ShellQuote(src.Path), ShellQuote(newPath))
			// Keep action as move/copy, redirect to newPath inside the directory
			op.RenamedDestPath = newPath
		}
	default:
		p.logDebug("Skipping %s (unknown conflict strategy, defaulting to skip)", ShellQuote(src.Path))
		op.Copy = false
		op.DeleteSrc = false
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
