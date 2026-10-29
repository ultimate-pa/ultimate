#!/bin/bash
DIR="$(dirname "${BASH_SOURCE[0]}")"
ARCH="32bit"

# Test verification
echo "---- Verification ----"
for PROGRAM in "${DIR}/examples"/*.c; do
  for SPEC in "${DIR}/examples"/*.prp; do
    "${DIR}/Ultimate.py" --file "${PROGRAM}" --spec "${SPEC}" --architecture "${ARCH}"
  done
done

# Test validation (for YAML correctness witness)
echo "---- Validation ----"
for WITNESS in "${DIR}/examples"/*.yml; do
  for SPEC in "${DIR}/examples"/*.prp; do
    "${DIR}/Ultimate.py" --file "${WITNESS%.*}.c" --witness-type correctness_witness --validate "${WITNESS}" --spec "${SPEC}" --architecture "${ARCH}"
  done
done
