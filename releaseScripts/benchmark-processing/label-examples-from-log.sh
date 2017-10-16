#!/bin/bash
# First argument: an IncrementalLogWithVMParameter log filename 
# Second argument: a search string in the UltimateResult part, e.g. "ShortDescription: All specifications hold"
# Third argument: the absolute path to a directory that should be used as prefix to the input file names found in the IncrementalLogWithVMParameter
# Fourth argument: a keyword that should be inserted in the first line of each matching input file
# If there is already a labeling, this script will not add a new label if the old one is already present. 

if [ -z "$1" ]; then
    echo "Missing first argument: path to IncrementalLogWithVMParameter"
	exit 1
fi
if [ -z "$2" ]; then
    echo "Missing second argument: search string"
	exit 1
fi
if [ -z "$3" ]; then
    echo "Missing third argument: absolute path prefix"
	exit 1
fi
if [ -z "$4" ]; then
    echo "Missing fourth argument: keyword that should be inserted"
	exit 1
fi

logfilename="${1}"
searchstring="${2}"
workingdir="${3}"
keyword="${4}"

grep -E UltimateResult "${logfilename}" | grep -E "${searchstring}" | grep -oE "Input:.*" | cut -d' ' -f 1 | cut -d':' -f 2 | sort -u | uniq | \
while read line
do
	file=${workingdir}${line}
	if [[ -f "$file" ]]; then
		echo "Processing $file"
		./label-example.sh "${file}" "${keyword}"
	fi
	
done 
