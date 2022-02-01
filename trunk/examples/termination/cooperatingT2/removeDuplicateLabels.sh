#!/bin/bash
# Many files from the CooperatingT2 benchmark set contain duplicate labels.
# This script removes them.
# Date: 2015-03-04
# Author: Matthias Heizmann

files=`find "$1" -name "*.c"|sort`

for f in $files;
do
    uniq "$f" > "$f".tmp
    mv "$f".tmp "$f"
done;

