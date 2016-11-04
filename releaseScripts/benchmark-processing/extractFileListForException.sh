#!/bin/bash

# Extracts a file list for a given exception from a TraceAbstractionTestSummary
# file.

if [ $# -ne 2 ]; then
	echo "Usage: ./extractFileListForException.sh <TA-Summary.log> <Exception String>"
	echo
	echo "Example:"
	echo "   ./extractFileListForException.sh TASummary.log \"IllegalArgumentException: Unhandled type ~NTSTATUS\""
	echo
	echo "This will print a list of all files that failed because of this exception."
	echo "This list can then be inserted into an Ultimate TestSuite for debugging."
	exit 1
fi

INPUT="$1"
STRING="$2"

OFS=$IFS
IFS=$'\n'
RES=( ""$(grep -B1 -e ".*ExpectedResult.*${STRING}" "${INPUT}" | grep "Input:" | sed -e 's/^\W*//;s/\W*$//' | sed -e 's/^.*Input:\(.*\) Settings:.*/\1/' | sort | uniq)"" )
IFS=$OFS

for ((i = 0; i < ${#RES[@]}; i++)); do
	FILE="${RES[$i]}"
	echo "\"examples/$FILE\","
done
