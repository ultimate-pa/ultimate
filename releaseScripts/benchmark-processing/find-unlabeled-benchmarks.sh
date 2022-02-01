#!/bin/bash 
# Scan SVCOMP benchmarks for files that are not labeled a certain way, i.e., that have not yet been marked terminating or overflowing 
# Use awk '!x[$0]++' to remove duplicates without sorting 

exec 3< <(find "$1" -type f -iname '*.set')

while read -u 3 file
do 
    
    while IFS='' read -r line || [[ -n "$line" ]]; do
        if [ ! -n "$line" ]; then 
            continue 
        fi
        
        if [[ "$line" == "#*" ]]; then 
            continue 
        fi

        find "$1" -type f ! -iname '*_true-termination*' -a ! -iname '*_false-termination*' -a -ipath "*$line" | sed 's/\(.*\)/<include>\1<\/include>/g'
    done < "$file"
done 
