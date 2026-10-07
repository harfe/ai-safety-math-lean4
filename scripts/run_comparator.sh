#!/usr/bin/env bash

####
# run `comparator` on all files in comparator_configs/claimed
####

# script fails if a single command fails
set -eu

# change directory to the script location
cd "$(dirname "$0")"
# then go to parent directory
cd ../


if [[ $# == 0 ]] || [[ $1 == --help ]]; then
  echo "Usage: $0 --claimed or $0 <file.json>"
  exit 0
fi

# lake, landrun, comparator, lean4export should be in $PATH:
command -v lake
command -v landrun
command -v comparator
command -v lean4export


main_run() {
  local json_file="$1"
  test -f "$json_file"

  # use command recommended by https://github.com/leanprover/comparator/blob/master/README.md
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory "$(pwd)" -- bash -c 'lake env comparator $1' _ "$json_file"

  # lake env comparator "$json_file"

  echo ""
  echo "$json_file passed"
  echo ""

}

if [[ $1 == --all ]] || [[ $1 == --claimed ]]; then
  test -f comparator_configs/claimed

  # main loop: go through lines in comparator_configs/claimed
  # each line should be a json file
  while read -u 10 line; do
    fname="comparator_configs/$line"
    test -f "$fname"
    main_run "$fname"


  done 10<comparator_configs/claimed
else
  main_run "$1"
fi
