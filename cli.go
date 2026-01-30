package main

import (
	"fmt"
	"os"
	"strings"

	"github.com/alecthomas/kong"
)

type CLI struct {
	Paths       []string `arg:"" name:"paths" help:"Source [...] Destination" required:""`
	Sources     []string `kong:"-"`
	Destination string   `kong:"-"`

	FileOverFile   string `help:"File conflict strategy"`
	FileOverFolder string `help:"File over folder strategy" default:"merge"`
	FolderOverFile string `help:"Folder over file strategy" default:"merge"`

	Copy     bool `help:"Copy instead of move" short:"c"`
	Simulate bool `help:"Simulate without making changes" aliases:"dry-run" short:"n"`
	Workers  int  `help:"Number of parallel workers" default:"4" aliases:"threads" short:"j"`
	Verbose  int  `help:"Verbose output (0-2)" short:"v" type:"counter"`

	Ext       []string `help:"Filter by file extensions" short:"e"`
	Exclude   []string `help:"Exclude patterns" short:"E"`
	Include   []string `help:"Include patterns" short:"I"`
	Size      []string `help:"Filter by file size (fd-find syntax: -S+5M, -S-10M, -S5M%10)" short:"S" aliases:"sizes"`
	Limit     int      `help:"Limit number of files transferred" short:"l"`
	SizeLimit string   `help:"Limit total size of files transferred (e.g., 100M, 1G)" aliases:"sl"`

	RelativeTo string `help:"Preserve directory hierarchy relative to path"`
	Relative   bool   `help:"Shortcut for --relative-to=/"`

	Parent bool `help:"Include parent folder name" short:"P"`
	BSD    bool `help:"rsync/BSD mv behavior (src trailing slash matters)"`

	DestBSD    bool `help:"BSD destination mode (default)"`
	DestFolder bool `help:"Destination is always a folder" aliases:"folder" short:"t"`
	DestFile   bool `help:"Destination is a file (no-target-directory)" aliases:"file" short:"T"`

	Version kong.VersionFlag `help:"Print version information and exit"`
}

func (c *CLI) AfterApply() error {
	if c.FileOverFile == "" {
		if c.Copy {
			c.FileOverFile = "skip-hash rename-dest"
		} else {
			c.FileOverFile = "delete-src-hash rename-dest"
		}
	}

	if c.Relative {
		c.RelativeTo = "/"
	}

	if c.Ext != nil {
		// make sure all extensions start with a dot
		for i, ext := range c.Ext {
			if !strings.HasPrefix(ext, ".") {
				c.Ext[i] = "." + ext
			}
		}
	}

	if len(c.Paths) < 2 {
		return fmt.Errorf("at least one source and one destination directory are required")
	}
	c.Sources = c.Paths[:len(c.Paths)-1]
	c.Destination = c.Paths[len(c.Paths)-1]

	if c.DestFolder {
		info, err := os.Stat(c.Destination)
		if err == nil && !info.IsDir() {
			// Only error if strategies don't allow fixing this
			canFix := strings.Contains(c.FolderOverFile, "delete-dest") ||
				strings.Contains(c.FolderOverFile, "rename-dest") ||
				strings.Contains(c.FolderOverFile, "merge") ||
				strings.Contains(c.FileOverFile, "delete-dest") ||
				strings.Contains(c.FileOverFile, "rename-dest")

			if !canFix {
				return fmt.Errorf("destination %s exists but is not a directory, and conflict strategies do not allow replacement", c.Destination)
			}
		}
	}

	if c.DestFile && len(c.Sources) > 1 {
		return fmt.Errorf("cannot use --dest-file with multiple sources")
	}

	return nil
}

type FileOverFileOpt string

const (
	SkipHash          FileOverFileOpt = "skip-hash"
	SkipSize          FileOverFileOpt = "skip-size"
	SkipLarger        FileOverFileOpt = "skip-larger"
	SkipSmaller       FileOverFileOpt = "skip-smaller"
	DeleteDestHash    FileOverFileOpt = "delete-dest-hash"
	DeleteDestSize    FileOverFileOpt = "delete-dest-size"
	DeleteDestLarger  FileOverFileOpt = "delete-dest-larger"
	DeleteDestSmaller FileOverFileOpt = "delete-dest-smaller"
	DeleteSrcHash     FileOverFileOpt = "delete-src-hash"
	DeleteSrcSize     FileOverFileOpt = "delete-src-size"
	DeleteSrcLarger   FileOverFileOpt = "delete-src-larger"
	DeleteSrcSmaller  FileOverFileOpt = "delete-src-smaller"
)

type FileOverFileMode string

const (
	FFSkip       FileOverFileMode = "skip"
	FFRenameSrc  FileOverFileMode = "rename-src"
	FFRenameDest FileOverFileMode = "rename-dest"
	FFDeleteSrc  FileOverFileMode = "delete-src"
	FFDeleteDest FileOverFileMode = "delete-dest"
)

type ConflictMode string

const (
	CSkip       ConflictMode = "skip"
	CRenameSrc  ConflictMode = "rename-src"
	CRenameDest ConflictMode = "rename-dest"
	CDeleteSrc  ConflictMode = "delete-src"
	CDeleteDest ConflictMode = "delete-dest"
	CMerge      ConflictMode = "merge"
)

type FileOverFileStrategy struct {
	Optionals []FileOverFileOpt
	Required  FileOverFileMode
}

func parseSizeFilter(sizes []string) func(int64) bool {
	if len(sizes) == 0 {
		return func(int64) bool { return true }
	}

	return func(size int64) bool {
		for _, constraint := range sizes {
			if !checkSizeConstraint(size, constraint) {
				return false
			}
		}
		return true
	}
}
