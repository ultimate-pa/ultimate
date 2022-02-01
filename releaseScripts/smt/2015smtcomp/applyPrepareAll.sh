#!/bin/bash
# Date: 2015-05-02
# Author: Matthias Heizmann
# Apply smtinterpol-prepare.jar to folder rename all .prep.smt2 files
# to .smt2 files.

for f in `find "$1"*.smt2`;
do
    java -jar /home/matthias/ultimate/releaseScripts/smt/2015smtcomp/smtinterpol-prepare.jar --track app "$f"
    mv "${f%%.smt2}.prep.smt2" "$f"
    perl /home/matthias/ultimate/releaseScripts/smt/2015smtcomp/MainTrack-Automizer.pl "$f"
    echo "(exit)" >> "$f"
done;
