#!/bin/sh

for i in *.ats; do 
	echo "minimizeSevpa(removeUnreachable(nwa));" >> "$i"
	echo "shrinkNwa(removeUnreachable(nwa));" >> "$i"
	echo "minimizeNwaPmaxSat(removeUnreachable(nwa));" >> "$i"
	echo "minimizeNwaPmaxSatAsymmetric(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDirectSimulation(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDelayedSimulation(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDirectSimulationB(removeUnreachable(nwa));" >> "$i"
	echo "ReduceNwaDelayedSimulationB(removeUnreachable(nwa));" >> "$i"
done