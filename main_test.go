package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
)

type testTree map[string]interface{}

func createTestTree(t *testing.T, root string, tree testTree) {
	for name, content := range tree {
		path := filepath.Join(root, name)
		switch v := content.(type) {
		case string:
			if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(path, []byte(v), 0o644); err != nil {
				t.Fatal(err)
			}
		case testTree:
			if err := os.MkdirAll(path, 0o755); err != nil {
				t.Fatal(err)
			}
			createTestTree(t, path, v)
		}
	}
}

func readTestTree(t *testing.T, root string) testTree {
	tree := make(testTree)
	entries, err := os.ReadDir(root)
	if err != nil {
		return tree
	}
	for _, entry := range entries {
		path := filepath.Join(root, entry.Name())
		if entry.IsDir() {
			tree[entry.Name()] = readTestTree(t, path)
		} else {
			content, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			tree[entry.Name()] = string(content)
		}
	}
	return tree
}

func compareTrees(t *testing.T, name string, got, want testTree) {
	t.Helper()
	for k, wantV := range want {
		gotV, ok := got[k]
		if !ok {
			t.Errorf("%s: missing key %q", name, k)
			continue
		}
		switch wantVal := wantV.(type) {
		case string:
			gotStr, ok := gotV.(string)
			if !ok {
				t.Errorf("%s[%q]: want string, got %T", name, k, gotV)
				continue
			}
			if gotStr != wantVal {
				t.Errorf("%s[%q]: got %q, want %q", name, k, gotStr, wantVal)
			}
		case testTree:
			gotTree, ok := gotV.(testTree)
			if !ok {
				t.Errorf("%s[%q]: want tree, got %T", name, k, gotV)
				continue
			}
			compareTrees(t, name+"/"+k, gotTree, wantVal)
		}
	}
	for k := range got {
		if _, ok := want[k]; !ok {
			t.Errorf("%s: unexpected key %q", name, k)
		}
	}
}

func TestSimpleMove(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{
		"file1.txt": "content1",
		"dir1": testTree{
			"file2.txt": "content2",
		},
	})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	// srcPaths, _ := scanDirectory(src, srcFS) // Removed
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	want := testTree{
		"file1.txt": "content1",
		"dir1": testTree{
			"file2.txt": "content2",
		},
	}

	got := readTestTree(t, dest)
	compareTrees(t, "dest", got, want)
}

func TestFileConflictSkip(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "new"})
	createTestTree(t, dest, testTree{"file.txt": "old"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	p := NewProgram(cli)

	// Pre-populate destFS to simulate existing destination state if needed for conflict detection
	// In the real app, main() does this.
	// But processSource also scans destination if needed or relies on destFS being populated.
	// We need to implement a helper if we want to pre-scan dest.
	// For testing, let's just make sure destFS knows about files in dest.
	// Or rely on processSource lazy loading via simulation?
	// The original main() does:
	// destFS := NewFileSystem()
	// if info, err := os.Stat(cli.Destination); err == nil { ... add root ... }
	// And then planMerge() -> scanDirectory(src)
	// But wait, planMerge used to utilize a populated destFS.
	// Now processSource uses a simulation which copies from destFS.
	// So we should populate destFS.
	scanTestDir(dest, destFS)

	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{"file.txt": "old"}
	compareTrees(t, "dest", got, want)
}

func scanTestDir(root string, fs *FileSystem) {
	filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
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
		return nil
	})
}

func TestFileConflictDeleteDest(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "new"})
	createTestTree(t, dest, testTree{"file.txt": "old"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "delete-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{"file.txt": "new"}
	compareTrees(t, "dest", got, want)
}

func TestFileConflictRenameSrc(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "new"})
	createTestTree(t, dest, testTree{"file.txt": "old"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "rename-src",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file.txt":   "old",
		"file_1.txt": "new",
	}
	compareTrees(t, "dest", got, want)
}

func TestFileConflictRenameDest(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "new"})
	createTestTree(t, dest, testTree{"file.txt": "old"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "rename-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file_1.txt": "old",
		"file.txt":   "new",
	}
	compareTrees(t, "dest", got, want)
}

func TestHashSkipEarlyDifferent(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	// Create large files with different content
	// Sample hash should detect difference without full hash
	largeContent1 := strings.Repeat("A", 1024*1024) // 1MB of A's
	largeContent2 := strings.Repeat("B", 1024*1024) // 1MB of B's

	createTestTree(t, src, testTree{"large.bin": largeContent1})
	createTestTree(t, dest, testTree{"large.bin": largeContent2})

	// Program will track hashes in its stats

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip-hash rename-src",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Should have detected difference with sample hash only
	if p.stats.SampleHashes == 0 {
		t.Error("Expected sample hashes to be used")
	}
	if p.stats.FullHashes != 0 {
		t.Errorf("Expected no full hashes for different files, got %d", p.stats.FullHashes)
	}

	// Files are different, so should not skip
	if p.stats.FilesProcessed == 0 {
		t.Error("Expected files to be processed")
	}
}

func TestHashSkipFullHashIdentical(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	// Create large identical files
	// Sample hash will match, then full hash confirms
	largeContent := strings.Repeat("identical data here\n", 100*1024) // ~2MB

	createTestTree(t, src, testTree{"large.bin": largeContent})
	createTestTree(t, dest, testTree{"large.bin": largeContent})

	// Program will track hashes in its stats

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip-hash skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Should have used both sample and full hashes
	if p.stats.SampleHashes == 0 {
		t.Error("Expected sample hashes to be used")
	}
	if p.stats.FullHashes == 0 {
		t.Error("Expected full hashes to confirm identical files")
	}

	// Should skip identical files
	if p.stats.FilesProcessed > 0 {
		// FilesProcessed counts transfers/moves. If skipped, it shouldn't increment?
		// Check processSource implementation.
		// If action is skip, we return nil in executeOperation, no stats increment.
		t.Errorf("Expected no files processed for identical files, got %d", p.stats.FilesProcessed)
	}
}

func TestHashDeleteDest(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "identical"})
	createTestTree(t, dest, testTree{"file.txt": "identical"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "delete-dest-hash rename-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{"file.txt": "identical"}
	compareTrees(t, "dest", got, want)
}

func TestSizeComparison(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "larger content here"})
	createTestTree(t, dest, testTree{"file.txt": "small"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip-larger skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Source is larger, should be skipped
	got := readTestTree(t, dest)
	want := testTree{"file.txt": "small"}
	compareTrees(t, "dest", got, want)
}

func TestDeleteSrcSmaller(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "small"})
	createTestTree(t, dest, testTree{"file.txt": "larger content here"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "delete-src-smaller skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Source should be deleted, dest unchanged
	got := readTestTree(t, dest)
	want := testTree{"file.txt": "larger content here"}
	compareTrees(t, "dest", got, want)
}

func TestMultipleSources(t *testing.T) {
	tmpDir := t.TempDir()
	src1 := filepath.Join(tmpDir, "src1")
	src2 := filepath.Join(tmpDir, "src2")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src1, 0o755)
	os.MkdirAll(src2, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src1, testTree{
		"file1.txt":  "from-src1",
		"shared.txt": "src1-version",
	})

	createTestTree(t, src2, testTree{
		"file2.txt":  "from-src2",
		"shared.txt": "src2-version",
	})

	cli := &CLI{
		Sources:        []string{src1},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	// Process src1
	// Process src1
	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src1, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Process src2
	cli.Sources = []string{src2}
	srcFS2 := NewFileSystem()

	// Reuse destFS which should have been updated by processSource (via pointer)
	// Actually, processSource updates destFS by copying simFS back to it?
	// Wait, I didn't implement copying back in previous step fully correct or test it.
	// In main() we do destFS = simFS.
	// In the new processSource, we copy back to destFS at the end.

	err = p.processSource(src2, srcFS2, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file1.txt":  "from-src1",
		"file2.txt":  "from-src2",
		"shared.txt": "src1-version",
	}

	compareTrees(t, "dest", got, want)
}

func TestSimulation(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "content"})
	srcBefore := readTestTree(t, src)

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "delete-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Simulate:       true,
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Verify src unchanged
	srcAfter := readTestTree(t, src)
	compareTrees(t, "src", srcAfter, srcBefore)

	// Verify dest unchanged
	destAfter := readTestTree(t, dest)
	if len(destAfter) != 0 {
		t.Error("dest should be empty in simulation mode")
	}
}

func TestCopyMode(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "content"})
	srcBefore := readTestTree(t, src)

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		Copy:           true,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Verify src unchanged
	srcAfter := readTestTree(t, src)
	compareTrees(t, "src", srcAfter, srcBefore)

	// Verify dest has copy
	destAfter := readTestTree(t, dest)
	want := testTree{"file.txt": "content"}
	compareTrees(t, "dest", destAfter, want)
}

func TestFileOverFolder(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"conflict": "is-file"})
	createTestTree(t, dest, testTree{
		"conflict": testTree{
			"file.txt": "in-folder",
		},
	})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "rename-dest",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"conflict_1": testTree{
			"file.txt": "in-folder",
		},
		"conflict": "is-file",
	}

	compareTrees(t, "dest", got, want)
}

func TestFolderOverFile(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{
		"conflict": testTree{
			"file.txt": "in-folder",
		},
	})
	createTestTree(t, dest, testTree{"conflict": "is-file"})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "rename-dest",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"conflict_1": "is-file",
		"conflict": testTree{
			"file.txt": "in-folder",
		},
	}

	compareTrees(t, "dest", got, want)
}

func TestEmptyFileOverwrite(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{"file.txt": "content"})
	createTestTree(t, dest, testTree{"file.txt": ""})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Empty files should be overwritten
	got := readTestTree(t, dest)
	want := testTree{"file.txt": "content"}
	compareTrees(t, "dest", got, want)
}

// TestParallelRace removed as it relied on internal planning structures
// specific to the old architecture and is adequately covered by other tests
// running with high worker counts.

func TestFilters(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{
		"file.txt":    "text",
		"file.go":     "go code",
		"exclude.txt": "ignore me",
		"include.log": "keep me",
	})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		Ext:            []string{".txt", ".log"},
		Exclude:        []string{"exclude*"},
		Include:        []string{"*"}, // Include all that match ext
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file.txt":    "text",
		"include.log": "keep me",
	}
	compareTrees(t, "dest", got, want)
}

func TestPathFlags(t *testing.T) {
	tmpDir := t.TempDir()
	srcBase := filepath.Join(tmpDir, "src_base")
	srcParent := filepath.Join(srcBase, "parent")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(srcParent, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, srcParent, testTree{
		"sub/file.txt": "content",
	})

	// Test -P (Parent)
	t.Run("ParentFlag", func(t *testing.T) {
		os.RemoveAll(srcParent)
		os.RemoveAll(dest)
		os.MkdirAll(srcParent, 0o755)
		os.MkdirAll(dest, 0o755)
		createTestTree(t, srcParent, testTree{
			"sub/file.txt": "content",
		})

		cli := &CLI{
			Sources:        []string{srcParent},
			Destination:    dest,
			Parent:         true,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		p := NewProgram(cli)
		err := p.processSource(srcParent, srcFS, NewFileSystem())
		if err != nil {
			t.Fatal(err)
		}

		got := readTestTree(t, dest)
		want := testTree{
			"parent": testTree{
				"sub": testTree{
					"file.txt": "content",
				},
			},
		}
		compareTrees(t, "dest", got, want)
	})

	// Test --relative-to
	t.Run("RelativeTo", func(t *testing.T) {
		os.RemoveAll(srcParent)
		os.RemoveAll(dest)
		os.MkdirAll(srcParent, 0o755)
		os.MkdirAll(dest, 0o755)
		createTestTree(t, srcParent, testTree{
			"sub/file.txt": "content",
		})

		cli := &CLI{
			Sources:        []string{srcParent},
			Destination:    dest,
			RelativeTo:     srcBase,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		p := NewProgram(cli)
		err := p.processSource(srcParent, srcFS, NewFileSystem())
		if err != nil {
			t.Fatal(err)
		}

		got := readTestTree(t, dest)
		want := testTree{
			"parent": testTree{
				"sub": testTree{
					"file.txt": "content",
				},
			},
		}
		compareTrees(t, "dest", got, want)
	})
}

func TestLimit(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{
		"file1.txt": "c1",
		"file2.txt": "c2",
		"file3.txt": "c3",
	})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		Limit:          2,
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	if len(got) != 2 {
		t.Errorf("Expected exactly 2 files moved, got %d", len(got))
	}
}

func TestSizeLimit(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	createTestTree(t, src, testTree{
		"file1.txt": strings.Repeat("a", 1024), // 1K
		"file2.txt": strings.Repeat("b", 1024), // 1K
		"file3.txt": strings.Repeat("c", 1024), // 1K
	})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		SizeLimit:      "1.5K",
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	got := readTestTree(t, dest)
	// Should move file1 (1K), then plannedBytes reaches 1K.
	// Next is file2 (1K), plannedBytes (1K) < maxBytes (1.5K), so it moves file2.
	// plannedBytes becomes 2K.
	// Next is file3 (1K), plannedBytes (2K) >= maxBytes (1.5K), so it breaks.
	if len(got) != 2 {
		t.Errorf("Expected exactly 2 files moved by size limit, got %d", len(got))
	}
}

func TestHumanToBytes(t *testing.T) {
	tests := []struct {
		input string
		want  int64
	}{
		{"100", 100 * 1024 * 1024}, // default case
		{"100b", 100},
		{"1k", 1024},
		{"1.5K", 1536},
		{"1m", 1024 * 1024},
		{"1G", 1024 * 1024 * 1024},
		{"  2.5 m  ", 2621440},
	}

	for _, tt := range tests {
		got := humanToBytes(tt.input)
		if got != tt.want {
			t.Errorf("humanToBytes(%q) = %d, want %d", tt.input, got, tt.want)
		}
	}
}

func TestSampleHashMiddleDifference(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	// Create 1MB files.
	// chunkSize is 64KB. sampling starts for size > 640KB.
	size := 1024 * 1024
	content1 := make([]byte, size)
	for i := range content1 {
		content1[i] = 'A'
	}
	content2 := make([]byte, size)
	copy(content2, content1)
	// Change one byte in the middle.
	// 512KB is exactly a sampling point (0.5 * size when numSamples=10)
	content2[512*1024] = 'B'

	createTestTree(t, src, testTree{"large.bin": string(content1)})
	createTestTree(t, dest, testTree{"large.bin": string(content2)})

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		FileOverFile:   "skip-hash rename-src",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	destFS := NewFileSystem()
	scanTestDir(dest, destFS)

	p := NewProgram(cli)
	err := p.processSource(src, srcFS, destFS)
	if err != nil {
		t.Fatal(err)
	}

	// Should have used sample hashes and NOT skipped because they are different
	if p.stats.SampleHashes == 0 {
		t.Error("Expected sample hashes to be used")
	}
	if p.stats.FullHashes != 0 {
		t.Error("Expected NO full hashes because sample hash should have detected difference")
	}

	// Should process 1 file (move)
	if p.stats.FilesProcessed == 0 {
		t.Error("Expected file to be processed")
	}
}

func TestBSDMove(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src_folder")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)
	createTestTree(t, src, testTree{"file.txt": "content"})

	// library merge-mv --bsd folder1  folder2/  # folder1 will be moved to folder2/folder1/
	t.Run("NoTrailingSlashMovesInto", func(t *testing.T) {
		os.RemoveAll(src)
		os.RemoveAll(dest)
		os.MkdirAll(src, 0o755)
		os.MkdirAll(dest, 0o755)
		createTestTree(t, src, testTree{"file.txt": "content"})

		cli := &CLI{
			Sources:        []string{src}, // No trailing slash
			Destination:    dest,
			BSD:            true,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		p := NewProgram(cli)
		p.processSource(src, srcFS, NewFileSystem())

		got := readTestTree(t, dest)
		want := testTree{
			"src_folder": testTree{
				"file.txt": "content",
			},
		}
		compareTrees(t, "dest", got, want)
	})

	// library merge-mv --bsd folder1/ folder2/  # folder1 will be merged with folder2/
	t.Run("TrailingSlashMerges", func(t *testing.T) {
		os.RemoveAll(src)
		os.RemoveAll(dest)
		os.MkdirAll(src, 0o755)
		os.MkdirAll(dest, 0o755)
		createTestTree(t, src, testTree{"file.txt": "content"})

		srcWithSlash := src + string(filepath.Separator)
		cli := &CLI{
			Sources:        []string{srcWithSlash},
			Destination:    dest,
			BSD:            true,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		p := NewProgram(cli)
		p.processSource(srcWithSlash, srcFS, NewFileSystem())

		got := readTestTree(t, dest)
		want := testTree{
			"file.txt": "content",
		}
		compareTrees(t, "dest", got, want)
	})
}

func TestComplexMergeScenarios(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")

	// Folder Over File with Merge strategy
	t.Run("FolderOverFileMerge", func(t *testing.T) {
		os.RemoveAll(src)
		os.RemoveAll(dest)
		createTestTree(t, src, testTree{
			"conflict": testTree{
				"file2.txt": "2",
			},
		})
		createTestTree(t, dest, testTree{"conflict": "1"})

		cli := &CLI{
			Sources:        []string{src},
			Destination:    dest,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		destFS := NewFileSystem()
		scanTestDir(dest, destFS)

		p := NewProgram(cli)
		p.processSource(src, srcFS, destFS)

		got := readTestTree(t, dest)
		// The file "conflict" should be renamed to "conflict_1" and the folder "conflict" should be created
		want := testTree{
			"conflict_1": "1",
			"conflict": testTree{
				"file2.txt": "2",
			},
		}
		compareTrees(t, "dest", got, want)
	})

	// File Over Folder with Merge strategy
	t.Run("FileOverFolderMerge", func(t *testing.T) {
		os.RemoveAll(src)
		os.RemoveAll(dest)
		createTestTree(t, src, testTree{"f1": "1"})
		createTestTree(t, dest, testTree{"f1": testTree{"file2": "2"}})

		cli := &CLI{
			Sources:        []string{src},
			Destination:    dest,
			FileOverFile:   "skip",
			FileOverFolder: "merge",
			FolderOverFile: "merge",
			Workers:        4,
		}
		srcFS := NewFileSystem()
		destFS := NewFileSystem()
		scanTestDir(dest, destFS)

		p := NewProgram(cli)
		p.processSource(src, srcFS, destFS)

		got := readTestTree(t, dest)
		// f1(file) moved into f1(folder) as f1/f1
		want := testTree{
			"f1": testTree{
				"file2": "2",
				"f1":    "1",
			},
		}
		compareTrees(t, "dest", got, want)
	})
}

func TestMultiSourceSequential(t *testing.T) {
	tmpDir := t.TempDir()
	src1 := filepath.Join(tmpDir, "src1")
	src2 := filepath.Join(tmpDir, "src2")
	src3 := filepath.Join(tmpDir, "src3")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src1, 0o755)
	os.MkdirAll(src2, 0o755)
	os.MkdirAll(src3, 0o755)
	os.MkdirAll(dest, 0o755)

	// src1 places a file
	createTestTree(t, src1, testTree{"file1.txt": "content1"})
	// src2 also has a file1.txt, will conflict and we'll use rename-dest (default strategy)
	createTestTree(t, src2, testTree{"file1.txt": "content2"})
	// src3 has a file1_1.txt, will conflict with the rename produced by src2
	createTestTree(t, src3, testTree{"file1_1.txt": "content3"})

	cli := &CLI{
		Sources:        []string{src1, src2, src3},
		Destination:    dest,
		FileOverFile:   "rename-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	p := NewProgram(cli)
	destFS := NewFileSystem()

	for _, src := range cli.Sources {
		srcFS := NewFileSystem()
		err := p.processSource(src, srcFS, destFS)
		if err != nil {
			t.Fatal(err)
		}
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file1.txt":   "content2",
		"file1_1.txt": "content3",
		"file1_2.txt": "content1",
	}

	compareTrees(t, "dest", got, want)
	if t.Failed() {
		fmt.Printf("\nDEBUG GOT: %+v\n", got)
	}
}

func TestMultiSourceIdenticalSkip(t *testing.T) {
	tmpDir := t.TempDir()
	src1 := filepath.Join(tmpDir, "src1")
	src2 := filepath.Join(tmpDir, "src2")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src1, 0o755)
	os.MkdirAll(src2, 0o755)
	os.MkdirAll(dest, 0o755)

	content := "identical content"
	createTestTree(t, src1, testTree{"file.txt": content})
	createTestTree(t, src2, testTree{"file.txt": content})

	cli := &CLI{
		Sources:      []string{src1, src2},
		Destination:  dest,
		FileOverFile: "skip-hash rename-src", // Skip if identical, else rename
		Workers:      1,
	}

	p := NewProgram(cli)
	destFS := NewFileSystem()

	for _, src := range cli.Sources {
		srcFS := NewFileSystem()
		err := p.processSource(src, srcFS, destFS)
		if err != nil {
			t.Fatal(err)
		}
	}

	got := readTestTree(t, dest)
	want := testTree{
		"file.txt": content,
	}

	compareTrees(t, "dest", got, want)

	// Since it's a move, src1/file.txt should be gone, and src2/file.txt should STILL BE THERE (skipped)
	if _, err := os.Stat(filepath.Join(src2, "file.txt")); os.IsNotExist(err) {
		t.Error("src2/file.txt should still exist because it should have been skipped")
	}
}

func TestSymlinks(t *testing.T) {
	tmpDir := t.TempDir()
	src := filepath.Join(tmpDir, "src")
	dest := filepath.Join(tmpDir, "dest")
	os.MkdirAll(src, 0o755)
	os.MkdirAll(dest, 0o755)

	targetFile := filepath.Join(tmpDir, "target.txt")
	os.WriteFile(targetFile, []byte("target content"), 0o644)

	// Create a symlink in src
	linkPath := filepath.Join(src, "link.txt")
	if err := os.Symlink(targetFile, linkPath); err != nil {
		t.Skip("Symlinks not supported on this filesystem")
	}

	cli := &CLI{
		Sources:        []string{src},
		Destination:    dest,
		Copy:           true, // Use copy to test link creation
		FileOverFile:   "skip",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        4,
	}

	srcFS := NewFileSystem()
	p := NewProgram(cli)
	err := p.processSource(src, srcFS, NewFileSystem())
	if err != nil {
		t.Fatal(err)
	}

	// Verify dest has a symlink pointing to the same target
	destLink := filepath.Join(dest, "link.txt")
	info, err := os.Lstat(destLink)
	if err != nil {
		t.Fatal(err)
	}
	if info.Mode()&os.ModeSymlink == 0 {
		t.Error("Expected dest/link.txt to be a symlink")
	}

	gotTarget, err := os.Readlink(destLink)
	if err != nil {
		t.Fatal(err)
	}
	if gotTarget != targetFile {
		t.Errorf("Expected link target %q, got %q", targetFile, gotTarget)
	}
}

func TestMultipleSourcesRace(t *testing.T) {
	// This test simulates a race condition where dependent operations are scheduled
	// (e.g. rename A -> B, then rename B -> C) and dispatched to different workers.
	// We use "rename-dest" strategy to force renames.
	// src1: populates dest with "file_i"
	// src2: contains "file_i" (causes rename dest/file_i -> dest/file_i_1)
	// src2: ALSO contains "file_i_1" (causes rename dest/file_i_1 -> dest/file_i_2)
	// If the second rename happens before the first rename is complete, it will fail.

	tmpDir := t.TempDir()
	src1 := filepath.Join(tmpDir, "src1")
	src2 := filepath.Join(tmpDir, "src2")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src1, 0o755)
	os.MkdirAll(src2, 0o755)
	os.MkdirAll(dest, 0o755)

	numFiles := 50 // Enough to likely trigger race with parallel workers

	// Setup src1
	for i := 0; i < numFiles; i++ {
		fname := fmt.Sprintf("file_%d", i)
		if err := os.WriteFile(filepath.Join(src1, fname), []byte("src1"), 0o644); err != nil {
			t.Fatal(err)
		}
	}

	// Setup src2
	for i := 0; i < numFiles; i++ {
		// file_i: will conflict with dest/file_i (from src1), causing dest/file_i -> dest/file_i_1
		fname := fmt.Sprintf("file_%d", i)
		if err := os.WriteFile(filepath.Join(src2, fname), []byte("src2_main"), 0o644); err != nil {
			t.Fatal(err)
		}

		// file_i_1: will conflict with dest/file_i_1 (created by above rename), causing dest/file_i_1 -> dest/file_i_2
		fnamesub := fmt.Sprintf("file_%d_1", i)
		if err := os.WriteFile(filepath.Join(src2, fnamesub), []byte("src2_sub"), 0o644); err != nil {
			t.Fatal(err)
		}
	}

	// Use rename-dest to trigger the dependency chain
	cli := &CLI{
		Sources:        []string{src1, src2},
		Destination:    dest,
		FileOverFile:   "rename-dest",
		FileOverFolder: "merge",
		FolderOverFile: "merge",
		Workers:        10, // Parallelism is key here
	}

	p := NewProgram(cli)
	destFS := NewFileSystem()

	// Run src1
	if err := p.processSource(src1, NewFileSystem(), destFS); err != nil {
		t.Fatalf("src1 processing failed: %v", err)
	}

	// Run src2 - this is where the race condition would occur
	if err := p.processSource(src2, NewFileSystem(), destFS); err != nil {
		t.Fatalf("src2 processing failed (race condition triggered?): %v", err)
	}

	// Validation
	count := 0
	filepath.Walk(dest, func(path string, info os.FileInfo, err error) error {
		if !info.IsDir() {
			count++
		}
		return nil
	})

	// Expected files per 'i':
	// dest/file_i (content: src2_main)
	// dest/file_i_1 (content: src2_sub)
	// dest/file_i_2 (content: src1 - originally file_i, renamed to _1, then to _2)
	expected := numFiles * 3
	if count != expected {
		t.Errorf("Expected %d files, got %d", expected, count)
	}
}

func TestConcurrentSourcesDestFSAccess(t *testing.T) {
	// This test attempts to simulate concurrent access to the shared destFS
	// by running processSource in parallel, which is not the standard flow
	// but tests robustness of the FileSystem locking.

	tmpDir := t.TempDir()
	src1 := filepath.Join(tmpDir, "src1")
	src2 := filepath.Join(tmpDir, "src2")
	dest := filepath.Join(tmpDir, "dest")

	os.MkdirAll(src1, 0o755)
	os.MkdirAll(src2, 0o755)
	os.MkdirAll(dest, 0o755)

	os.WriteFile(filepath.Join(src1, "file1.txt"), []byte("src1"), 0o644)
	os.WriteFile(filepath.Join(src2, "file2.txt"), []byte("src2"), 0o644)

	cli := &CLI{
		Destination:  dest,
		FileOverFile: "skip",
		Workers:      2,
	}

	p := NewProgram(cli)
	destFS := NewFileSystem()

	var wg sync.WaitGroup
	wg.Add(2)

	// Random start delay to interleave operations
	go func() {
		defer wg.Done()
		p.processSource(src1, NewFileSystem(), destFS)
	}()
	go func() {
		defer wg.Done()
		p.processSource(src2, NewFileSystem(), destFS)
	}()

	wg.Wait()

	// Check if both files exist (basic smoke test for crash/panic)
	if _, err := os.Stat(filepath.Join(dest, "file1.txt")); os.IsNotExist(err) {
		t.Error("file1.txt missing")
	}
	if _, err := os.Stat(filepath.Join(dest, "file2.txt")); os.IsNotExist(err) {
		t.Error("file2.txt missing")
	}
}
