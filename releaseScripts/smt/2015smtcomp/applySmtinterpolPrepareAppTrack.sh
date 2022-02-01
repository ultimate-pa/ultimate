#!/bin/bash
# Date: 2015-05-02
# Author: Matthias Heizmann
# Apply smtinterpol-prepare.jar to folder rename all .prep.smt2 files
# to .smt2 files.

for f in `find "$1"*.smt2`;
do
    java -jar smtinterpol-prepare.jar --track app "$f"
    mv "${f%%.smt2}.prep.smt2" "$f"
done;
