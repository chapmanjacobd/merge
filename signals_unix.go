//go:build !windows

package main

import (
	"os"
	"os/signal"
	"syscall"
)

func (p *Program) watchResize() {
	p.updateWidth()
	ch := make(chan os.Signal, 1)
	signal.Notify(ch, syscall.SIGWINCH)
	go func() {
		for range ch {
			p.updateWidth()
		}
	}()
}
