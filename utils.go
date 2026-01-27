package main

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

var safeChars = regexp.MustCompile(`^[a-zA-Z0-9!@%_+=:,./-]+$`)

func ShellQuote(s string) string {
	if s == "" {
		return "''"
	}
	if safeChars.MatchString(s) {
		return "'" + s + "'"
	}
	return "'" + strings.ReplaceAll(s, "'", "'\\''") + "'"
}

func truncateMiddle(s string, max int) string {
	if len(s) <= max {
		return s
	}
	if max < 3 {
		return s[:max]
	}
	half := (max - 1) / 2
	return s[:half] + "…" + s[len(s)-half:]
}

func bytes2human(n int64) string {
	const unit = 1024
	if n < unit {
		return fmt.Sprintf("%d B", n)
	}
	div, exp := int64(unit), 0
	for n >= unit*div && exp < 5 {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %ciB", float64(n)/float64(div), "KMGTPE"[exp])
}

func humanToBytes(inputStr string) int64 {
	inputStr = strings.TrimSpace(strings.ToLower(inputStr))
	if inputStr == "" {
		return 0
	}

	reVal := regexp.MustCompile(`^[0-9.]*`)
	reUnit := regexp.MustCompile(`[a-z]+`)

	valStr := reVal.FindString(inputStr)
	unitStr := reUnit.FindString(inputStr)

	value, err := strconv.ParseFloat(valStr, 64)
	if err != nil {
		return 0
	}

	var k int64 = 1024
	byteMap := map[string]int64{
		"b": 1,
		"k": k,
		"m": k * k,
		"g": k * k * k,
		"t": k * k * k * k,
		"p": k * k * k * k * k,
	}

	unit := "m"
	if len(unitStr) > 0 {
		unit = string(unitStr[0])
	}

	multiplier, ok := byteMap[unit]
	if !ok {
		multiplier = k * k // default to MB
	}

	return int64(value * float64(multiplier))
}
