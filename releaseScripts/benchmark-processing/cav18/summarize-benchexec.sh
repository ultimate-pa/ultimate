#!/bin/bash
# Summarize stats generated with benchexec and csv export of Ultimate 

# the result dir with a csv subdir 

while [[ $# -gt 0 ]]
do
    key="$1"
    case $key in
            -d|--dir)
            DIR="$2"
            shift 
            ;;
            -n|--name)
            NAME="$2"
            shift
            ;;
            *)
            # ignore unknown option
            echo "Unknown option $key"
            echo "Usage:"
            echo " -d|--dir     Set the directory you want to analyze"
            echo " -n|--name    Set a name for the temporary files"
            exit 1
            ;;
    esac
    shift # shift past argument or value
done

if [ -z ${DIR+x} ]; then echo "No directory specified" && exit 1; fi
if [ -z ${NAME+x} ]; then echo "No name specified" && exit 1; fi

DBBASENAME="$NAME-sqlcsv.db"
TABLE="$NAME" 
DB="sqlite:///$DBBASENAME"
DATE=`date +"%F %T"`

function join_by { local IFS="$1"; shift; echo "$*"; }

function exitOnFail {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        eerror "$@ failed with $1"
        eend $status
    fi
    eend $status
}

function createDb {
    if [ ! -f "$DBBASENAME" ]; then
        # this will create a sqlite db that contains the benchexec results s.t. each runset has a header like 
        # <name> (result) 
        # <name>_2 (cputime)
        # <name>_3 (walltime) 
        # <name>_4 (memUsage)
        sed '3d' "$DIR"results*table.csv | sed '1d' | csvsql --db "$DB" --tables $TABLE --insert
        return
    fi
    echo "$DBBASENAME already exists, assuming it is valid"
}

function getCsvType {
    declare -n retCsvType=$1
    number=1
    fnames=($(find "$DIR"/ -iname '*.csv' | grep -oP "Csv.*.csv" | cut -d "-" -f 1-2 | sort | uniq))
    for file in ${fnames[@]}; do 
        echo "$number)" ${fnames[$(($number-1))]}
        let "number += 1"
    done
    read -p "Select the type of csv you want to combine: " fid
    fid=$(($fid-1)) # reduce user input by 1 since array starts counting from zero
    retCsvType="${fnames[${fid}]}"
}


function getCombinedCsv {
    declare -n ret=$1
    getCsvType csvtype
    ret="$NAME-$csvtype-final.csv"

    if [ -f "$ret" ]; then
        echo "$ret exists, assuming it is valid"
        return
    fi
    
    chunks=50
    
    csvs=($(find "$DIR"/ -iname $csvtype*.csv))
    for (( i = 0 ; i < ${#csvs[@]} ; i=$i+$chunks )); do
        printf .
        for (( j = $i ; j < ${#csvs[@]} && j < $i+$chunks ; j=$j+1 )); do
            parentdirs+=("$(basename "$(dirname "${csvs[$j]}")")")
        done
        groups=$(join_by , ${parentdirs[@]})
        csvstack -g $groups ${csvs[@]:i:$chunks} > "$NAME-combined-$i.csv"
        unset parentdirs
    done 
    printf "\n"
    for file in "$NAME-combined-*.csv"; do
        comb+=("$file")
    done

    csvstack ${comb[@]} > "$ret"
    rm "$NAME-combined-"*
}

createDb
getCombinedCsv combinedFile

        # <name> (result) 
        # <name>_2 (cputime)
        # <name>_3 (walltime) 
        # <name>_4 (memUsage)
runsets=($(tail -n +2 "$DIR"results*table.csv | csvcut -n -t | cut -d: -f 2 | uniq | grep -v "run set"))

#for runset in ${runsets[@]}; do 
#    echo $runset
#    sql2csv --db "${DB}" --query "select count(*) as Count, $runset as Result from $TABLE group by $runset order by Result desc" 
#    echo ""
#done

for (( i = 0 ; i < ${#runsets[@]} ; i=$i+1 )); do
    runset="${runsets[$i]}"
    if [ -z ${query+x} ]; then 
        query="(select count(*) as Count$runset, $runset from $TABLE group by $runset) As t$i"
    else 
        let "j=$i-1"
        query="((select count(*) as Count$runset, $runset from $TABLE group by $runset) As t$i LEFT OUTER JOIN $query On t$i.$runset = t$j.${runsets[($j)]})"
    fi
done

for (( i = ${#runsets[@]}-1 ; i >= 0 ; i=$i-1 )); do
    runset="${runsets[$i]}"
    if [ -z ${columns+x} ]; then 
        columns="$runset as Result,Count$runset as $runset"
    else 
        columns+=",Count$runset as $runset"
    fi
done

sql2csv --db "${DB}" --query "select $columns from $query" | csvlook > bla




 