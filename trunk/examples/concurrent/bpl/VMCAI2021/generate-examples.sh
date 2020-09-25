#!/bin/bash

DIR=$(realpath $(dirname "$0"))/generated
MAX_THREADS=${1:-20}

mkdir -p "$DIR"
echo "Cleaning folder $DIR ..."
rm -rf $DIR/example2_N=*.bpl

echo "Generating $MAX_THREADS benchmarks ..."
for k in $(seq 1 $MAX_THREADS)
do
  printf -v k_pad "%02d" $k
  FILE="$DIR/example2_N=$k_pad.bpl"

  echo "// #Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;
" >> "$FILE"

  for i in $(seq 1 $k)
  do
    echo "  fork $i thread$i();" >> "$FILE"
  done

  for i in $(seq 1 $k)
  do
    echo "  join $i;" >> "$FILE"
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
  //while (*) {
    x := x + $i;
  //  x := x * $i;
  //}
}
" >> "$FILE"
  done
done
