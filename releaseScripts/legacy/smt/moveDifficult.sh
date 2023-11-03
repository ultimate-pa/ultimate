#!/bin/bash
# Date: 3.5.2014
# Author: Matthias Heizmann
# This script is used to construct SMT benchmarks from LassoRanker
# move all .smt2 files that contain the substring 
#     "Warning solver responded UNKNOWN to the check-sat above"
# to the subfolder "difficult"

for f in `ls *.smt2`;
do
	lineWithUnkown=`grep "Warning solver responded UNKNOWN to the check-sat above" "$f"`
	if [ "$lineWithUnkown" ]; then
		echo "difficult: $f"
		mv "$f" difficult/
	else
		echo "not difficult: $f"
	fi
done;

