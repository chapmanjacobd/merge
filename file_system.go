package main

import (
	"io/fs"
	"os"
	"path/filepath"
	"sync"
)

type FileSystem struct {
	mu      sync.RWMutex
	nodes   map[string]*FileNode
	checked map[string]bool
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

func NewFileSystem() *FileSystem {
	return &FileSystem{
		nodes:   make(map[string]*FileNode),
		checked: make(map[string]bool),
	}
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
