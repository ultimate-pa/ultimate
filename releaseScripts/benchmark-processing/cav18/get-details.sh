#!/bin/bash

# trap ctrl-c and call ctrl_c()
trap ctrl_c INT

function ctrl_c() {
    echo "Aborted"
    exit 2
}

csv="$1"
outcsv="out"

specs=($(csvcut -c File "$csv" | tail -n +2 | sort | uniq | grep -oP "\d\d\d\........\..*\.cil" | cut -d '.' -f 3 | sort | uniq))
settings=($(csvcut -c Settings "$csv" | tail -n +2 |sort | uniq)) 

header="Driver, Spec, Tasks, "
for setting in "${settings[@]}"; do 
    header+="Overall-$setting,Analysis-$setting,"
done
header+="Speedup Overall,Speedup Analysis"
echo "$header" > "$outcsv"
        
function makeFile(){
    local folder="$1"
    local spec="$2"
    local i="$3"
    local out="$i-$spec-$csv"
    csvcut -c 1-3,5-10,23,32,42,72,73,74,84,93,94 "$csv" | csvgrep -c Folder -m "$folder" | csvgrep -c File -m "$spec" > "$out"
    local lcount=$(wc -l "$out" | cut -d " " -f 1) 
    let lcount=$lcount-1
    if [ "$lcount" == "0" ]; then
        rm "$out"
        return
    fi
    tasks=$(echo "scale=0; ($lcount / ${#settings[@]}) + 1" | bc -lq)
    echo "$out has $lcount rows, $tasks tasks"
    lcount="$tasks"
    
    row="$folder,$spec,$lcount,"
    for setting in "${settings[@]}"; do 
        overall=$(csvgrep -c Settings -m "$setting" "$out" | csvcut -c OverallTime | csvstat --sum | sed 's/,//g')
        row+="$overall,"
        dump=$(csvgrep -c Settings -m "$setting" "$out" | csvcut -c DUMP_TIME | csvstat --sum | sed 's/,//g')
        if [ "$dump" != "None" ]; then 
            ana=$(echo "scale=0; ($overall - $dump) / 1000000" | bc -lq)
        else 
            ana=$(echo "scale=0; ($overall) / 1000000" | bc -lq)
            defaultana="$ana"
            defaultoverall="$overall"
        fi 
        row+="$ana,"
        if [[ "$setting" =~ .*LazyReuse.* ]]; then
            lazyana="$ana"
            lazyoverall="$overall"
        fi 
    done
    speedupana=$(echo "scale=2;$defaultana / $lazyana" | bc -lq)
    speedupoverall=$(echo "scale=2;$defaultoverall / $lazyoverall" | bc -lq)
    row+="$speedupoverall,$speedupana"
    echo "$row" >> "$outcsv"
    rm "$out"
}

i=1
folder="drivers--media--dvb--dvb-usb--dvb-usb-az6007.ko"
for spec in "${specs[@]}"; do 
    makeFile "$folder" "$spec" "$i"
done 

csvsort -r -c "Speedup Analysis" "$outcsv" > "tmp-$outcsv"
mv "tmp-$outcsv" "$outcsv"