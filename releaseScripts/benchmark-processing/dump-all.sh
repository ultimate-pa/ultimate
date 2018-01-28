#!/bin/bash 
# small script to dump all tracechecks where interpolants did not pass sanity check 

broken_logs=($(ack -l "generated interpolants did not pass sanity check" "$1"))

for log in ${broken_logs[@]}; do 
    file=`head -n 1 "$log" | grep -oP "\-i .* *"`
    java -Xmx6G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data -tc ../../../trunk/examples/toolchains/AutomizerC.xml -s ../../../trunk/examples/settings/cav18-smtinterpol/svcomp-DerefFreeMemtrack-32bit-Automizer_SmtInterpol_Array.epf -i ${file:2} --traceabstraction.dump.smt.script.to.file true --traceabstraction.to.the.following.directory ./dump
    last=`find ./dump -type f -iname '*.smt2' | sed -e 's/\(.*_\)\([[:digit:]]\+\)\(_Trace.\)*/\2\1\3/g' | sort -n | sed -e 's/\([[:digit:]]\+\)\(.*_\)\(_Trace.\)*/\2\1\3/g' | tail -n1`
    cp "$last" ./insane/
    rm ./dump/*
done



