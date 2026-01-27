package main

import (
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/term"
)

type Progress struct {
	start         time.Time
	lastPrintTime time.Time
	currentRel    atomic.Value // string
	termWidth     int
	mu            sync.Mutex
}

func (p *Program) logOp(op MergeOperation, root string) {
	finalDest := op.DestPath
	if op.RenamedDestPath != "" {
		finalDest = op.RenamedDestPath
	}

	rel := finalDest
	if root != "" {
		if r, err := filepath.Rel(root, finalDest); err == nil {
			rel = r
		}
	}

	action := op.Action
	if op.DeleteDest {
		action = "replace"
	}

	fmt.Fprintf(os.Stderr, "\n%-10s %s", action, rel)
}

func (p *Program) updateWidth() {
	w, _, err := term.GetSize(int(os.Stdout.Fd()))
	if err != nil {
		p.progress.termWidth = 80
		return
	}
	p.progress.mu.Lock()
	p.progress.termWidth = w
	p.progress.mu.Unlock()
}

func (p *Program) printProgress() {
	if p.cli.Verbose == 0 {
		return
	}

	files := atomic.LoadInt64(&p.stats.FilesProcessed)
	bytes := atomic.LoadInt64(&p.stats.BytesMoved)
	elapsed := time.Since(p.progress.start).Seconds()

	var rate float64
	if elapsed > 0 {
		rate = float64(bytes) / elapsed
	}

	status := fmt.Sprintf(
		"[Files: %d, %s] | %s/s",
		files,
		bytes2human(bytes),
		bytes2human(int64(rate)),
	)

	cur, _ := p.progress.currentRel.Load().(string)
	p.progress.mu.Lock()
	termWidth := p.progress.termWidth
	p.progress.mu.Unlock()

	remaining := termWidth - len(status) - 4
	if remaining > 10 && cur != "" {
		status += " | " + truncateMiddle(cur, remaining)
	}

	fmt.Fprint(os.Stderr, "\r"+status+"\033[K")
	p.progress.lastPrintTime = time.Now()
}
