#!/bin/bash

set -e

DIR=$(realpath $(dirname "$0"))
cd "$DIR"

# Read blacklisted benchmarks from file
if test -f blacklist.txt
then
  echo "Reading blacklist entries..."
  readarray -t BLACKLIST < blacklist.txt
  echo ""
else
  BLACKLIST=()
fi

# Clone repo with original benchmarks
git clone https://github.com/weaver-verifier/weaver.git weaver
echo ""

echo -n "Translating benchmarks"
for file in $(find "weaver/examples" -type f -name '*.wvr')
do
  if [[ " ${BLACKLIST[*]} " == *"$file"* ]]
  then
    # Do not translate blacklisted benchmark
    echo -n "-"
  else
    # Translate benchmark
    outfile="generated/${file#"weaver/examples/"}.bpl"
    outdir=$(dirname "$outfile")
    mkdir -p "$outdir"

    python3 "translate-weaver-benchmark.py3" "$file" "$outfile"
    echo -n "."
  fi
done
echo ""

# Cleanup
rm -rf "weaver"

echo "DONE."
