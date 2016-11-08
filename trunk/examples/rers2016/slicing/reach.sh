#!/bin/bash

INPUT=$1
FN=$(basename "$INPUT")
extension="${FN##*.}"
FN="${FN%.*}"

echo "Processing $FN..."
awk '/.*__VERIFIER_error\([0-9].*/ {print "/*@ assert 0; */"} {print $0}' $INPUT > tmpfiler$FN.c
frama-c -quiet -val -eva -slevel 15 tmpfiler$FN.c > result$FN.txt
grep assertion result$FN.txt | awk -F: '{ln=$2; cmd="sed -n " (ln+1) "p '"tmpfiler$FN.c"'"; cmd | getline line; print line " " $4}' -
rm -f tmpfiler$FN.c
