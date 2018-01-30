#!/bin/bash

settings=($(csvcut -c Settings "all.csv" | tail -n +2 | sort | uniq ))

c=0
#for j in "all.csv" "all-but-first.csv" "only-first.csv"; do 
for j in "all-but-first.csv"; do 
	echo "$j" 
    for i in "${settings[@]}"; do 
		echo "$i"
        csvgrep -c3 -m "$i" "$j" | csvcut -c DUMP_TIME,OverallTime | csvstat 
        let c=$c+1
    done 
done 

