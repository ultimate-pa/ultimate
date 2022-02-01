#!/bin/bash

out=`basename "$1"`".summary"
echo "$out"
bash get-benchexec-overview-nonUltimate.py.sh "$1" "*.log" > "$out"
for i in "$1"/*.xml; do 
    set=`echo $i | cut -d . -f 4`
    out=`basename "$1"`".summary.$set"
    echo "$out"
    bash get-benchexec-overview-nonUltimate.py.sh "$1" "$set*.log" > "$out"
done 