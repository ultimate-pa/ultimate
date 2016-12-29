#!/bin/bash

xmlfile=`realpath ${1}`
toolname="$2"
outputfilename="$toolname"-error
toolupper="$(tr '[:lower:]' '[:upper:]' <<< ${toolname:0:1})${toolname:1}"

mkdir tmp 
cd tmp 
../../get-svcomp-xmls.sh "$xmlfile"
../../getunsounds.py
../../get-error-files.sh "" "$toolname" > ${outputfilename}
cd ..

cat tmp/${outputfilename} | sed "s/tmp.*\(${toolupper}.*xml\)/\1/g" | sort > ${outputfilename}

# cleanup temp files 
rm -r tmp