#! /bin/bash

# Extracts sifa statistic results from a given list of log files and creates a csv file.
# The csv file is written to an outfile in the working directory.
#
# The csv contains the paths (!) of the used files.
# Therefore if the paths contain information like dates or git hashes you don't have to annotate the csv again with these informations.

outfile="$(mktemp sifaStats-XXXXXX.csv)"
echo "Writing output to $(readlink -f "$outfile")"

removeUnits() {
	# units after the numbers make it harder to process the data ==> remove them
	sed 's/s$//'
}

grep -Fx -m1 -A1 -Z '  - StatisticsResult: Symbolic Interpretation with Fluid Abstractions' "$@" |
sed -En '2~3s/(.*)\x0 */FILE \1\n/p' |
sed -E '2~2s/([^,]+) ([^,]+)(, |$)/\2 \1\n/g' |
removeUnits |
mlr --ixtab --ocsv unsparsify > "$outfile"

echo "Done"
echo "Time statistics for this tool"
times
