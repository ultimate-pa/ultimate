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

# Read expected verdicts from file
DEFAULT_VERDICT_ULTIMATE="Safe"
DEFAULT_VERDICT_SVCOMP="true"
if test -f verdicts.txt
then
  echo "Reading expected verdicts..."
  readarray -t VERDICTS < verdicts.txt
  echo ""
else
  echo -e "No verdicts found. Assuming '$DEFAULT_VERDICT_ULTIMATE' for all benchmarks.\n"
  VERDICTS=()
fi

# Clone repo with original benchmarks
git clone https://github.com/weaver-verifier/weaver.git weaver
echo ""

echo "Translating benchmarks ( '_' = blacklisted, '+' = safe, '-' = unsafe, '#' = default verdict ) :"
for file in $(find "weaver/examples" -type f -name '*.wvr')
do
  if [[ " ${BLACKLIST[*]} " == *"$file"* ]]
  then
    # Do not translate blacklisted benchmark
    echo -n "_"
  else
    # Translate benchmark
    outfile="generated/${file#"weaver/examples/"}.bpl"
    outdir=$(dirname "$outfile")
    mkdir -p "$outdir"
    python3 "translate-weaver-benchmark.py3" "$file" "$outfile"

    # Determine verdict and include in file
    if [[ " ${VERDICTS[*]} " == *"$file:Safe"* ]]
    then
      VERDICT_ULTIMATE="Safe"
      VERDICT_SVCOMP="true"
      echo -n "+"
    elif [[ " ${VERDICTS[*]} " == *"$file:Unsafe"* ]]
    then
      VERDICT_ULTIMATE="Unsafe"
      VERDICT_SVCOMP="false"
      echo -n "-"
    else
      VERDICT_ULTIMATE="$DEFAULT_VERDICT_ULTIMATE"
      VERDICT_SVCOMP="$DEFAULT_VERDICT_SVCOMP"
      echo -n "#"
    fi
    echo -e "//#$VERDICT_ULTIMATE\n$(cat "$outfile")" > "$outfile"

    # Generate yml file
    NAME=$(basename $outfile)
    PROPFILE=$(realpath -s --relative-to="$(dirname $outfile)" "../../../svcomp/properties/unreach-call.prp")
    echo "format_version: '2.0'

input_files: '$NAME'

properties:
  - property_file: $PROPFILE
    expected_verdict: $VERDICT_SVCOMP

options:
  language: Boogie
" > "${outfile%".bpl"}.yml"
  fi
done
echo ""

# Cleanup
rm -rf "weaver"

echo -e "\nDONE."
