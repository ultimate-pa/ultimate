#!/bin/bash

for file in `find "$1" -type f -iname "*.log"`; do 
    if grep -q "StatisticsResult: ArrayEqualityDomainStatistics" "$file"; then 
        #echo "$file"
        head -n 1 "$file" | grep -oP "\-i.*" | cut -d " " -f 2
    fi
done | sort | uniq 
