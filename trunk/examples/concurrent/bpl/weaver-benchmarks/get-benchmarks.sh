#!/bin/bash

DIR=$(realpath $(dirname "$0"))

set -e

# Clone repo with original benchmarks
git clone https://github.com/weaver-verifier/weaver.git "$DIR/weaver"

echo -n "Translating benchmarks"
for file in $(find "$DIR/weaver/examples" -type f -name '*.wvr')
do
  outfile="$DIR/generated/${file#"$DIR/weaver/examples/"}.bpl"
  outdir=$(dirname "$outfile")
  mkdir -p "$outdir"

  python3 "$DIR/translate-weaver-benchmark.py3" "$file" "$outfile"
  echo -n "."
done
echo -e "\nDONE."

rm -rf "$DIR/weaver"
