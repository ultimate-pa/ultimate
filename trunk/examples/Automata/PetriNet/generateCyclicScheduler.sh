#! /bin/bash

# Print a cyclic scheduler in Ultimate's .ats format.
# See comments in printed .ats file for more information.
#
# author: schaetzc@tf.uni-freiburg.de
# date:   2018-07-13

printUsage() {
	echo "usage: $(basename "$0") <n>"
	echo "       where n is a positive integer"
	echo "Print a cyclic scheduler for n threads in Ultimate's .ats format."
}

isPositiveInteger() {
	[[ "$1" =~ ^[0-9]*[1-9][0-9]*$ ]]
}

(( "$#" == 1 )) && isPositiveInteger "$1" || { printUsage; exit 1; }
n="$1"

prev() {
	prev="$1"
	if (( --prev < 1 )); then
		prev="$n"
	fi
	echo "$prev"
}

next() {
	next="$1"
	if (( ++next > n )); then
		next=1
	fi
	echo "$next"
}

places=()
initialPlaces=(s1)
transitions=()
dummyLetter=a

for this in $(seq "$n"); do
	prev="$(prev "$this")"
	next="$(next "$this")"
	places+=({s,p,q}"$this")
	initialPlaces+=(p"$this")
	transitions+=(
		"{s$this p$this} $dummyLetter {s$next q$this}"
		"{q$this} $dummyLetter {p$this}"
	)
done

cat <<EOF 
// cyclic scheduler for $n threads 
// auto-generated on $(date --iso) by $USER using $(basename "$0")
//
// Based on the solution of task 1.1.c in
// https://www7.in.tum.de/um/courses/petri/SS2015/exercises/sol1.pdf

print(numberOfConditions(finitePrefix(cyclicScheduler$n)));

PetriNet cyclicScheduler$n = (
  alphabet = {$dummyLetter},
  places = {${places[@]}},
  transitions = {
$(printf '    (%s)\n' "${transitions[@]}")
  },
  initialMarking = {${initialPlaces[@]}},
  acceptingPlaces = {}
);
EOF



