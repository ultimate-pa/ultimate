#!/bin/sh

for i in *.ats; do 
	echo "minimizeSevpa(removeUnreachable(nwa));" >> "$i"
	echo "shrinkNwa(removeUnreachable(nwa));" >> "$i"
	echo "minimizeNwaMaxSat2(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDirectSimulation(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDelayedSimulation(removeUnreachable(nwa));" >> "$i"
done