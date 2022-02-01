#!/bin/bash 
# small script to dump all tracechecks where interpolants did not pass sanity check 
# $1 string for which we should extract logs 
# $2 folder where the results are (possibly globbed) 


broken_logs=($(ack -l "$1" "$2"))

for log in ${broken_logs[@]}; do 
    cli=`head -n 1 "$log"`
    cli+=" --traceabstraction.dump.smt.script.to.file true --traceabstraction.to.the.following.directory ./dump"
    eval $cli
    last=`find ./dump -type f -iname '*.smt2' | sed -e 's/\(.*_\)\([[:digit:]]\+\)\(_Trace.\)*/\2\1\3/g' | sort -n | sed -e 's/\([[:digit:]]\+\)\(.*_\)\(_Trace.\)*/\2\1\3/g' | tail -n1`
    cp "$last" ./insane/
    rm ./dump/*
done



