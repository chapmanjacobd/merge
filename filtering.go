package main

import (
	"path/filepath"
	"strconv"
	"strings"
)

func (p *Program) shouldInclude(path string, node *FileNode) bool {
	name := filepath.Base(path)
	if len(p.cli.Ext) > 0 {
		match := false
		for _, ext := range p.cli.Ext {
			if strings.HasSuffix(name, ext) {
				match = true
				break
			}
		}
		if !match {
			return false
		}
	}

	if len(p.cli.Include) > 0 {
		match := false
		for _, pattern := range p.cli.Include {
			if matched, _ := filepath.Match(pattern, name); matched {
				match = true
				break
			}
		}
		if !match {
			return false
		}
	}

	if len(p.cli.Exclude) > 0 {
		for _, pattern := range p.cli.Exclude {
			if matched, _ := filepath.Match(pattern, name); matched {
				return false
			}
		}
	}

	// Check size constraints using cached GetInfo
	if len(p.cli.Size) > 0 {
		size, err := node.GetSize()
		if err != nil {
			return false
		}
		if !p.sizeFilter(size) {
			return false
		}
	}

	return true
}

func checkSizeConstraint(size int64, constraint string) bool {
	constraint = strings.TrimSpace(constraint)
	if constraint == "" {
		return true
	}

	// Handle percentage constraints (e.g., "5M%10" means 5MB ±10%)
	if strings.Contains(constraint, "%") {
		parts := strings.Split(constraint, "%")
		if len(parts) != 2 {
			return true // Invalid format, skip
		}
		targetSize := humanToBytes(parts[0])
		percent, err := strconv.ParseFloat(parts[1], 64)
		if err != nil {
			return true // Invalid percent, skip
		}
		lowerBound := int64(float64(targetSize) * (1 - percent/100))
		upperBound := int64(float64(targetSize) * (1 + percent/100))
		return size >= lowerBound && size <= upperBound
	}

	// Handle comparison operators
	if strings.HasPrefix(constraint, ">") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, ">"))
		return size > threshold
	}
	if strings.HasPrefix(constraint, "<") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "<"))
		return size < threshold
	}
	if strings.HasPrefix(constraint, "+") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "+"))
		return size > threshold
	}
	if strings.HasPrefix(constraint, "-") {
		threshold := humanToBytes(strings.TrimPrefix(constraint, "-"))
		return size <= threshold
	}

	// Exact match
	threshold := humanToBytes(constraint)
	return size == threshold
}
