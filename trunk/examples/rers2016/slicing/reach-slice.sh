#!/bin/bash

INPUT=$1
FN=$(basename "$INPUT")
extension="${FN##*.}"
FN="${FN%.*}"

echo "Processing $FN..."
awk '/.*__VERIFIER_error\([0-9].*/ {print "/*@ slice pragma stmt; */"} {print $0}' $INPUT > tmpfiler$FN.c
frama-c -quiet -slevel 10 -slice-pragma errorCheck tmpfiler$FN.c -then-on 'Slicing export' -print -ocode "$FN-reach.c" > /dev/null
awk '/.*__VERIFIER_error\([0-9].*/ {print $0}' "$FN-reach.c"
rm -f tmpfiler$FN.c
