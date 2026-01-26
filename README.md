# Merge

A high-performance Go implementation for merging folders with preconfigured conflict resolution.

## Install

    go install github.com/chapmanjacobd/merge@latest

## Features

### Core Capabilities

- Copy or Move: Choose between copy or move merging folder trees
- Simulation: Pre-flight simulation ensures safe operations
- Parallel Operations: Concurrent file processing with configurable worker threads
- Multiple Sources: Merge multiple source folders into a single destination
- Smart Hash Comparison: Two-stage hashing (sample → full) for efficient deduplication checks

### Conflict Resolution

#### File Over File (14 strategies)

When a file conflicts with another file:

Optional Conditions (evaluated first):

- `skip-hash` - Skip if SHA-256 hash matches
- `skip-size` - Skip if file size matches
- `skip-larger` - Skip if source is larger
- `skip-smaller` - Skip if source is smaller
- `delete-dest-hash` - Delete destination if hash matches
- `delete-dest-size` - Delete destination if size matches
- `delete-dest-larger` - Delete destination if larger
- `delete-dest-smaller` - Delete destination if smaller
- `delete-src-hash` - Delete source if hash matches
- `delete-src-size` - Delete source if size matches
- `delete-src-larger` - Delete source if larger
- `delete-src-smaller` - Delete source if smaller

Required Fallback (one must be specified):

- `skip` - Skip the source file
- `rename-src` - Rename source to file_1.ext
- `rename-dest` - Rename destination to file_1.ext, move source to file.ext
- `delete-src` - Delete source file
- `delete-dest` - Delete destination, move source

Default: "delete-src-hash rename-dest"

#### File Over Folder

When a file conflicts with a folder:

- `skip` - Keep folder, skip file
- `rename-src` - Rename file to name_1
- `rename-dest` - Rename folder to name_1/, place file
- `delete-src` - Delete file
- `delete-dest` - Delete folder tree
- `merge` - Move file into folder as folder/folder

Default: "merge"

#### Folder Over File

When a folder conflicts with a file:

- `skip` - Keep file, skip folder
- `rename-dest` - Rename file, place folder
- `delete-src` - Delete folder tree
- `delete-dest` - Delete file
- `merge` - Move file into folder as folder/file

Default: "merge"

## Usage

### Basic Examples

```bash
# Move Merge
merge src/ dest/

# Copy Merge
merge --copy src/ dest/

# Multiple sources
merge src1/ src2/ src3/ dest/

# Simulate first (dry run)
merge --simulate --verbose src/ dest/
```

### Conflict Resolution Examples

```bash
# Skip identical files by hash, rename conflicts
merge --file-over-file "skip-hash rename-dest" src/ dest/

# Keep larger files, delete smaller ones
merge --file-over-file "delete-src-smaller delete-dest" src/ dest/

# Multi-stage: skip if hash matches, else keep larger, else rename
merge --file-over-file "skip-hash delete-dest-smaller rename-dest" src/ dest/

# Always replace destination
merge --file-over-file "delete-dest" src/ dest/

# Trust destination is newer
merge --file-over-file "delete-src-hash skip" src/ dest/
```

### Advanced Options

```bash
# Parallel workers
merge -j 8 src/ dest/

# Verbose output
merge -vv src/ dest/

# File extension filtering
merge -eJPG -ePNG photos/ archive/

# Include/exclude patterns
merge -E "*.tmp" -I "important/*" src/ dest/

# Limit number of files
merge -l 1000 src/ dest/

# Custom handling of folder conflicts
merge \
  --file-over-file "skip-hash rename-dest" \
  --file-over-folder "merge" \
  --folder-over-file "rename-dest" \
  src/ dest/
```
