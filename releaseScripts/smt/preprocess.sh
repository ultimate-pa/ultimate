#!/bin/bash
# Date: 15.5.2014
# Author: Matthias Heizmann
# Preprocess smt scripts for SMT-COMP
# The first argument should be the (perl) script that is setting the correct
# logic and inserting the set-info source.
# 

for f in *.smt2;
do
    "$1" "$f"
    java -jar smtinterpol-prepare.jar --track app "$f"
    mv "${f%%.smt2}.prep.smt2" "$f"
done;
