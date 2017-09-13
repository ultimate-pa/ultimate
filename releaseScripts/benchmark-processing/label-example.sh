#!/bin/bash
# Specify a filename as first argument and a keyword that should be written in the first line of the file as second argument.
# If there is already a labeling, this script will not add a new label if the old one is already present. 

ALLOWED_LABELS=(
"Safe"
"Unsafe"
"Terminating"
"Nonterminating"
)

infile="$1"
keyword="$2" 


function checkKeyword(){
	for (( i = 0 ; i < ${#ALLOWED_LABELS[@]} ; i=$i+1 ));
	do
		if [[ "${ALLOWED_LABELS[${i}]}" == "$1" ]]; then
			return 0
		fi
	done
	return 1
}

function processFileContent(){
	local file="${1}"
		
	current=`head -n 1 "${file}"`
	if [[ ${current} == //\#* ]]; then 
		# there is already a labeling, check if we do not label multiple times 
		if [[ ${current} == *"${keyword}"* ]]; then 
			echo "Already labeled with ${keyword} (label is ${current})"
			return 0
		fi
		sed -i "1s/.*/\/\/${current:2} #${keyword}/" "${file}"
	else
		sed -i "1s/^/\/\/#${keyword}\n/" "${file}"
	fi
	return 0
}

function processFile(){
	local line="$1"
	
	if [ -f "${line}" ]; then
		processFileContent "${line}"
	else
		target=`echo "$line" | rev | cut -d'/' -f 1 | rev`
		if [[ -z "${target// }" ]]; then 
			echo "${target} is empty, skipping..."
			return 1
		fi 
		
		results=($(find . | ack "$target"))
		
		if [ ${#results[@]} -eq 0 ]; then
			echo "Could not resolve partial file name $target"
			return 1
		fi
	
		
		for (( i = 0 ; i < ${#results[@]} ; i=$i+1 ));
		do
			processFileContent "${results[${i}]}"
		done
	fi 	
}

if ! checkKeyword "${keyword}"; then 
	echo "Illegal keyword: ${keyword} (allowed is ${ALLOWED_LABELS[*]})"
	exit 1
fi 

if processFile "${infile}"; then
	exit 0
else	
	exit 1
fi
