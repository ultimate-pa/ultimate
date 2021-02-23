#!/bin/bash

set -e

DIR=$(realpath $(dirname "$0"))
cd "$DIR"

# Clone repo with original benchmarks
git clone https://github.com/weaver-verifier/weaver.git weaver

echo -n "Translating benchmarks"
for file in $(find "weaver/examples" -type f -name '*.wvr')
do
  outfile="generated/${file#"weaver/examples/"}.bpl"
  outdir=$(dirname "$outfile")
  mkdir -p "$outdir"

  python3 "translate-weaver-benchmark.py3" "$file" "$outfile"
  echo -n "."
done
echo -e "\nDONE."

rm -rf "weaver"
