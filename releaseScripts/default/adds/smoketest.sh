#!/bin/bash
DIR="$(dirname "${BASH_SOURCE[0]}")"

for file in "$DIR"/examples/*.c; do
  for spec in "$DIR"/examples/*.prp; do
    "$DIR"/Ultimate.py --file "$file" --spec "$spec" --architecture 32bit
  done
done
