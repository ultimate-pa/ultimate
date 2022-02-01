#!/bin/bash

Settings=(
"AutomizerCamel_Seq"
"AbsInt_Seq"
"AbsInt_imprecise_Seq"
"AbsInt_Seq_Inl"
"AbsInt_imprecise_Seq_Inl"
"AbsInt_SS"
"AbsInt_imprecise_SS"
"AbsInt_LFB"
"AbsInt_imprecise_LFB"
)


for j in ${Settings[@]}; do
    echo "$j"
    for i in `find "$1" -type f -iname "$j\.*.log"`; do  
        grep -oP "\s+\- \w*Result\w*" "$i"; 
    done |sort |uniq -c
done 