#!/usr/bin/env bash

## Create html files from the .md files

# script fails if a single command fails
set -eu

# change directory to the script location
cd "$(dirname "$0")"
# then go to parent directory
cd ../

cd Articles

# pandoc should be in $PATH
which pandoc

mkdir -p html


for file in *.md; do
  outfile="html/${file%.*}.html"
  pandoc "$file" -f gfm+tex_math_dollars -t html -s --katex -o "$outfile"
  echo converted "$file"

done

