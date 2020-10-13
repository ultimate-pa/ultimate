#!/bin/bash

DIR=$(realpath $(dirname "$0"))/generated
MAX_THREADS=${1:-20}

mkdir -p "$DIR"
echo "Cleaning folder $DIR ..."

# Delete files following old naming schema, if any left
rm -rf $DIR/example2_N=*.bpl
rm -rf $DIR/example2_N=*.yml
# Delete files following new naming schema
rm -rf $DIR/example_*.bpl
rm -rf $DIR/example_*.yml

echo "Generating $MAX_THREADS benchmarks ..."
for k in $(seq 1 $MAX_THREADS)
do
  printf -v k_pad "%02d" $k
  NAME="example_$k_pad"

  FILE="$DIR/$NAME.bpl"

  echo "// #Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;
" >> "$FILE"

  unset THREAD_ID
  declare -a THREAD_ID

  for i in $(seq 1 $k)
  do
    # Construct a thread ID as i-tuple of value i.
    # This way, there is only one compatible join!
    ID=""
    for j in $(seq 1 $i)
    do
      ID="$ID$i"
      if (( j < i ))
      then
        ID="$ID,"
      fi
    done
    THREAD_ID+=("$ID")

    echo "  fork $ID thread$i();" >> "$FILE"
  done

  for id in "${THREAD_ID[@]}"
  do
    echo "  join $id;" >> "$FILE"
  done

  echo "
  assert x >= 0;
}
" >> "$FILE"

  for i in $(seq 1 $k)
  do
    echo "
procedure thread$i()
modifies x;
{
  while (*) {
    x := x + $i;
    x := x * $i;
  }
}
" >> "$FILE"
  done

  YAML="$DIR/$NAME.yml"
  echo "format_version: '1.0'

input_files: '$NAME.bpl'

properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true" >> "$YAML"
done
