#!/bin/bash
# Check all C files for syntax compatibility with C11
# Date: 16.10.2013
# Author: Matthias Heizmann

files=`find "$1" -name "*.c"|sort`

for f in $files;
do
    gcc -std=c11 -pedantic -Wsequence-point -fsyntax-only $f
done;

