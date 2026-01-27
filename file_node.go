package main

import (
	"os"

	"sync"
	"sync/atomic"
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
