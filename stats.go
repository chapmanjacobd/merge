package main

import (
	"fmt"

	"sync/atomic"
)

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
