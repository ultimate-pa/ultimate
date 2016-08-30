#!/bin/bash

INPUT=$1
FN=$(basename "$INPUT")
extension="${FN##*.}"
FN="${FN%.*}"

echo "Processing $FN..."
for ((i=0; i <= 99 ; i++)) do
    echo "Slice $i..."
    awk '/.*__VERIFIER_error\('"$i"'\).*/ {print "/*@ slice pragma stmt; */"} {print $0}' $INPUT > tmpfile$FN.c
    frama-c -quiet -slevel 5 -slice-pragma errorCheck tmpfile$FN.c -then-on 'Slicing export' -print -ocode "$FN-$i.c" > /dev/null
done
rm -f tmpfile$FN.c
