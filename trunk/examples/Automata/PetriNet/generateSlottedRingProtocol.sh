#! /bin/bash

# Print an n-slotted ring protocol in Ultimate's .ats format.
# See comments in printed .ats file for more information.
#
# author: schaetzc@tf.uni-freiburg.de
# date:   2018-07-11

printUsage() {
	echo "usage: $(basename "$0") <n>"
	echo "       where n is a positive integer"
	echo "Print an n-slotted ring protocol in Ultimate's .ats format."
}

isPositiveInteger() {
	[[ "$1" =~ ^[0-9]*[1-9][0-9]*$ ]]
}

(( "$#" == 1 )) && isPositiveInteger "$1" || { printUsage; exit 1; }
n="$1"

nodePrefix() {
	echo "n${1}_"
}

prevNodePrefix() {
	prev="$1"
	if (( --prev < 1 )); then
		prev="$n"
	fi
	nodePrefix "$prev"
}

nextNodePrefix() {
	next="$1"
	if (( ++next > n )); then
		next=1
	fi
	nodePrefix "$next"
}

places=()
initialPlaces=()
transitions=()
dummyLetter=a

for node in $(seq "$n"); do
	this="$(nodePrefix "$node")"
	prev="$(prevNodePrefix "$node")"
	next="$(nextNodePrefix "$node")"
	places+=("$this"{1..10})
	initialPlaces+=("$this"{2,6})
	transitions+=(
		# give free slot
		"{${this}1 ${this}4} $dummyLetter {${this}2 ${this}3}"
		# free
		"{${this}2 ${this}6} $dummyLetter {${this}5 ${next}8}"
		# ack
		"{${this}3} $dummyLetter {${prev}6}"
		# int ack
		"{${this}5} $dummyLetter {${this}4}"
		# other
		"{${this}7} $dummyLetter {${this}9}"
		# owner
		"{${this}7} $dummyLetter {${this}8}"
		# go on
		"{${this}8} $dummyLetter {${this}1}"
		# write
		"{${this}8} $dummyLetter {${this}9}"
		# put message in slot
		"{${this}4 ${this}9} $dummyLetter {${this}3 ${this}10}"
		# used
		"{${this}6 ${this}10} $dummyLetter {${this}5 ${next}7}"
	)
done

cat <<EOF 
// $n-slotted ring protocol
// auto-generated on $(date --iso) by $USER using $(basename "$0")
//
// The slotted ring protocol was presented in [1].
// In [2] the slotted ring protocol was used to show that complete finite
// prefixes can be drastically reduced in size. Exact numbers of conditions and
// events in the prefixes of some n-slotted ring protocols are given in
// table 2 on page 18 and can be used as a test for Ultimate's finite prefix
// operation.
//
// [1] E. Pastor, O. Roig, J. Cortadella and R.M. Badia:
//     Petri Net Analysis Using Boolean Manipulation.
//     https://doi.org/10.1007/3-540-58152-9_23
//
// [2] Javier Esparza, Stefan Römer, and Walter Vogler:
//     An improvement of McMillan's unfolding algorithm
//     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.1.9584

print(numberOfConditions(finitePrefix(slottedRingProtocol$n)));

PetriNet slottedRingProtocol$n = (
  alphabet = {$dummyLetter},
  places = {${places[@]}},
  transitions = {
$(printf '    (%s)\n' "${transitions[@]}")
  },
  initialMarking = {${initialPlaces[@]}},
  acceptingPlaces = {}
);
EOF



