#!/bin/bash
# Check all C files for syntax compatibility with C99
# Date: 16.10.2013
# Author: Matthias Heizmann

files=`find "$1" -name "*.c"|sort`

for f in $files;
do
    gcc -std=c99 -pedantic -fsyntax-only $f
done;

