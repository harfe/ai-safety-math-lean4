#!/usr/bin/env bash

# script fails if a single command fails
set -eu

# change directory to the script location
cd "$(dirname "$0")"
# then go to parent directory
cd ../


# lake, landrun, comparator, lean4export should be in $PATH:
which lake
which landrun
which comparator
which lean4export


test -f comparator_configs/successful


# main loop: go through lines in comparator_configs/successful
# each line should be a json file
while read line; do
  fname="comparator_configs/$line"
  test -f "$fname"

  # use command recommended by https://github.com/leanprover/comparator/blob/master/README.md
  # (except we use "" isntead of '')
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c "lake env comparator $fname"

  # lake env comparator "$fname"

  echo ""
  echo "$fname passed"
  echo ""

done <comparator_configs/successful

