#!/bin/bash
DIR="$(dirname "${BASH_SOURCE[0]}")"

# Test verification
echo "---- Verification ----"
for file in "$DIR"/examples/*.c; do
  for spec in "$DIR"/examples/*.prp; do
    "$DIR"/Ultimate.py --file "$file" --spec "$spec" --architecture 32bit
  done
done

# Test validation (for YAML correctness witness)
echo "---- Validation ----"
for witness in "$DIR"/examples/*.yml; do
  for spec in "$DIR"/examples/*.prp; do
    "$DIR"/Ultimate.py --file "${witness%.*}.c" --witness-type correctness_witness --validate "$witness" --spec "$spec" --architecture 32bit
  done
done
