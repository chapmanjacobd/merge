//go:build windows

package main

import (
	"time"
)

func (p *Program) watchResize() {
	p.updateWidth()
	go func() {
		ticker := time.NewTicker(800 * time.Millisecond)
		defer ticker.Stop()
		for range ticker.C {
			p.updateWidth()
		}
	}()
}
