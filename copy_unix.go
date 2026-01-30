//go:build !windows

package main

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
)

func copyFile(src, dst string) error {
	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
		return err
	}

	cmd := exec.Command("cp", "-pT", src, dst)
	if out, err := cmd.CombinedOutput(); err != nil {
		if _, err := os.Stat(src); err == nil {
			_ = os.Remove(dst)
		}
		return fmt.Errorf("cp failed: %s", bytes.TrimSpace(out))
	}
	return nil
}
