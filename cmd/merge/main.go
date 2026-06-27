package main

import (
	"fmt"
	"os"

	"github.com/alecthomas/kong"
	"github.com/chapmanjacobd/merge"
)

func main() {
	cli := &merge.CLI{}
	kong.Parse(cli,
		kong.Name("merge"),
		kong.Description("Merge folders with apriori conflict resolution"),
		kong.UsageOnError(),
		kong.Vars{
			"version": merge.GetVersion(),
		},
	)

	if err := merge.Run(cli); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}
