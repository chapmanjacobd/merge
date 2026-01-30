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
	rel := op.DestPath
	if root != "" {
		if r, err := filepath.Rel(root, op.DestPath); err == nil {
			rel = r
		}
	}

	if p.cli.Verbose < 2 && !p.cli.Simulate {
		return
	}

	action := ""
	if op.DeleteSrc && !op.Copy {
		action = "delete"
	} else if op.DeleteDest {
		action = "replace"
	} else if op.Copy {
		if op.RenamedDestPath != "" {
			action = "rename"
		} else if op.DeleteSrc {
			action = "move"
		} else {
			action = "copy"
		}
	}

	sizeStr := ""
	if !op.IsDir {
		node := op.SrcNode
		if node == nil {
			node = &FileNode{Path: op.SrcPath}
		}
		if sz, err := node.GetSize(); err == nil {
			sizeStr = fmt.Sprintf(" (%s)", bytes2human(sz))
		}
	}

	if action != "" {
		p.printLog(fmt.Sprintf("%-10s %s%s", action, ShellQuote(rel), sizeStr))
	}
}

func (p *Program) logDebug(format string, a ...interface{}) {
	if p.cli.Verbose >= 2 {
		p.printLog(fmt.Sprintf("DEBUG: "+format, a...))
	}
}

func (p *Program) printLog(msg string) {
	p.clearProgress()
	fmt.Fprintln(os.Stderr, msg)
	// Optionally reprint progress immediately?
	// Usually better to let the next ticker handle it to avoid flickering,
	// unless the log rate is low.
}

func (p *Program) clearProgress() {
	if p.cli.Verbose > 0 {
		fmt.Fprint(os.Stderr, "\r\033[K")
	}
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

	files := atomic.LoadInt64(&p.stats.FilesMerged)
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

	// assume line is either empty or we are overwriting previous progress
	fmt.Fprint(os.Stderr, "\r"+status+"\033[K")
	p.progress.lastPrintTime = time.Now()
}
