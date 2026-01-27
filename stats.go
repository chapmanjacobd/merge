package main

import (
	"fmt"
	"sync/atomic"
)

type Stats struct {
	FilesMerged   int64
	FoldersMerged int64
	Conflicts     int64
	BytesMoved    int64
	Errors        int64
	SampleHashes  int64
	FullHashes    int64
}

func (s *Stats) Print() {
	FilesMerged := atomic.LoadInt64(&s.FilesMerged)
	FoldersMerged := atomic.LoadInt64(&s.FoldersMerged)
	conflicts := atomic.LoadInt64(&s.Conflicts)
	bytesMoved := atomic.LoadInt64(&s.BytesMoved)
	sampleHashes := atomic.LoadInt64(&s.SampleHashes)
	fullHashes := atomic.LoadInt64(&s.FullHashes)
	errors := atomic.LoadInt64(&s.Errors)

	plural := "files"
	if FilesMerged == 1 {
		plural = "file"
	}
	fmt.Printf("\nSummary:\n")
	fmt.Printf("  %d %s\n", FilesMerged, plural)
	fmt.Printf("  %d folders\n", FoldersMerged)
	fmt.Printf("  %d conflicts\n", conflicts)
	fmt.Printf("  %d bytes moved\n", bytesMoved)
	if sampleHashes > 0 || fullHashes > 0 {
		fmt.Printf("  %d sample hashes, %d full hashes\n", sampleHashes, fullHashes)
	}
	if errors > 0 {
		fmt.Printf("  %d errors\n", errors)
	}
}
