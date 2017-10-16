#!/bin/bash 
# small script to find files that contain certain statistics using the csvfix tool 
find . -type f -ipath '*Taipan+AI_EQ.epf_AutomizerC*Csv-TraceAbstractionBenchmarks*' |while read line; do 
#	isstrong=`csvfix exclude -f 1:30,32:100 "$line" | csvfix tail -n 1 `
	isstrong=`csvfix order -ifn -fn AbstIntStrong "$line" | csvfix tail -n 1 `
	if [ $isstrong != "\"0\"" ]; then 
		echo "$isstrong -- $line "
#		cat "$line"
#		echo "--"
	fi 
done 
