#!/bin/bash 
# small script to find files that contain certain statistics using the csvfix tool 
find . -type f -ipath '*Taipan+AI_EQ.epf_AutomizerC*Csv-TraceAbstractionBenchmarks*' | while read -r line; do
	isstrong=$(csvfix order -ifn -fn AbstIntStrong "$line" | csvfix tail -n 1)
	if [ "$isstrong" != "\"0\"" ]; then
		echo "$isstrong -- $line "
	fi
done 
