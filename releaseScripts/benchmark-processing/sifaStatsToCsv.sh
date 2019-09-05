#! /bin/bash

# Extracts sifa statistic results from a given list of log files and creates a csv file.
# The csv file is written to an outfile in the working directory.
#
# This script only works for BenchExec logs.
# Plain Ultimate logs do not work because of the leading "[2019-... INFO L123Class]: ".
#
# The paths passed as arguments to this script may neither contain "," nor ": "
# as these are used to separate fields from each otehr and keys and values from each other. 
#
# The csv contains the paths (literally, the arguments of this script) of the used files.
# Therefore if the paths contain information like dates or git hashes you don't have to annotate the csv again with these informations.



outfile="$(mktemp sifaStats-XXXXXX.csv)"
echo "Writing output to $(readlink -f "$outfile")"

grep -HFx -m1 -A1 -Z '  - StatisticsResult: Symbolic Interpretation with Fluid Abstractions' "$@" |
sed -En '2~3s/(.*)\x0 */FILE: \1, /p' |
mlr --idkvp --ifs ', ' --ips ': ' --ocsv unsparsify > "$outfile"

echo Done
times



echo
echo "Adding columns for percentual computation times"

dsl="$(
	head -n1 "$outfile" |
	grep -Eo '[^,]*_TIME\[ms\]' | grep -vFx 'OVERALL_TIME[ms]' |
	sed -E 's|(.*)\[ms\]| $["\1[%]"] = $["\1[ms]"] / $["OVERALL_TIME[ms]"];|'
)"
mlr -I --csv put "$dsl" "$outfile"

echo "Done"
times
