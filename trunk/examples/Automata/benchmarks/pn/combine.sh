#! /bin/bash

# Combines .ats files in the working directory for benchmarking
# difference operation Petri net \ DFA.
#
# File pairs of the following pattern are combined:
#
#     XXX_Iteration(i)_AbstractionAfterDifference.ats
#     XXX_Iteration(i+1)_EagerFloydHoareAutomaton.ats

renameNet() {
	sed 's/PetriNet nwa = (/PetriNet net = (/' "$@"
}

removeComments() {
	sed '/^\/\//d' "$@"
}

dumpDate() {
	grep -Pom1 '^// Testfile dumped by Ultimate at \K.*' "$@"
}

for minuend in *_Iteration*_AbstractionAfterDifference.ats; do
	[[ "$minuend" =~ (.*)_Iteration(.*)_AbstractionAfterDifference.ats ]]
	prefix="${BASH_REMATCH[1]}"
	i="${BASH_REMATCH[2]}"
	(( iPlusOne = i + 1 ))
	subtrahend="$prefix"_Iteration"$iPlusOne"_EagerFloydHoareAutomaton.ats
	if ! [ -f "$subtrahend" ]; then
		echo "Missing subtrahend for $minuend"
		continue
	fi
	difference="$prefix"_Difference_"$i"_"$iPlusOne".ats
	cat - <(removeComments "$minuend" | renameNet) <(removeComments "$subtrahend") > "$difference" <<-EOF
		// Benchmark for difference of Petri net and DFA  
		// Generated from
		// $minuend ($(dumpDate "$minuend"))
		// $subtrahend ($(dumpDate "$subtrahend"))
	EOF
done

