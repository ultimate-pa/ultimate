#! /bin/bash

# Print a petri net flower in Ultimate's .ats format.
# See comments in printed .ats file for more information.
#
# author: schaetzc@tf.uni-freiburg.de
# date:   2018-07-13

printUsage() {
	echo "usage: $(basename "$0") <stalkSize> <petalCount>"
	echo "       where stalkSize and petalCount are both non-negative integers"
	echo "Print a petri net flower in Ultimate's .ats format."
}

isNonNegativeInteger() {
	[[ "$1" =~ ^[0-9]+$ ]]
}

(( "$#" == 2 )) && isNonNegativeInteger "$1" && isNonNegativeInteger "$2" || { printUsage; exit 1; }
stalkSize="$1"
petalCount="$2"

alphabet=()
places=(s0)
initialPlaces=(s0)
transitions=()

lastStalk=0
for stalk in $(seq "$stalkSize"); do
	places+=(s"$stalk")
	alphabet+=("i$stalk")
	transitions+=("{s$lastStalk} "i$stalk" {s$stalk}")
	lastStalk="$stalk"
done

for petal in $(seq "$petalCount"); do
	alphabet+=("o$petal")
	transitions+=("{s$lastStalk} "o$petal" {s$lastStalk}")
	last="$this"
done

netName="flower_${stalkSize}_${petalCount}"


cat <<EOF 
// Petri net flower with stalk of length $stalkSize and $petalCount petals  
// auto-generated on $(date --iso) by $USER using $(basename "$0")
//
// The stalk is a chain of $stalkSize transitions.
// At the end of the chain, there are $petalCount petals.
// Each petal is a selfloop-transition. 

print(numberOfConditions(finitePrefix($netName)));

PetriNet $netName = (
  alphabet = {${alphabet[@]}},
  places = {${places[@]}},
  transitions = {
$([ -n "$transitions" ] && printf '    (%s)\n' "${transitions[@]}")
  },
  initialMarking = {${initialPlaces[@]}},
  acceptingPlaces = {}
);
EOF



