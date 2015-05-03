#!/bin/bash
# Date: 2015-05-02
# Author: Matthias Heizmann

for f in `find "$1"*.smt2`;
do
    echo "(exit)" >> "$f"
done;
