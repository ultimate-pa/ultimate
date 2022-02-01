#! /bin/bash

# Extracts sifa statistic results from a given list of log files and prints them to stdout.
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

grep -HFx -m1 -A1 -Z '  - StatisticsResult: Symbolic Interpretation with Fluid Abstractions' "$@" |
sed -En '2~3s/(.*)\x0 */FILE: \1, /p' |
mlr --idkvp --ifs ', ' --ips ': ' --ocsv unsparsify > "$outfile"

# Adding columns for percents/ratios

dsl="$(
	head -n1 "$outfile" |
	grep -Eo '[^,]*_TIME\[ms\]' | grep -vFx 'OVERALL_TIME[ms]' |
	grep -vF '_MAX_TIME[ms]' |
	sed -E 's|(.*)\[ms\]| $["\1[%]"] = $["\1[ms]"] / $["OVERALL_TIME[ms]"];|'
)"'
	$["DAG_COMPRESSION_RATIO"] = $["DAG_COMPRESSION_PROCESSED_NODES"] / $["DAG_COMPRESSION_RETAINED_NODES"];
	$["FLUID_YES_ANSWERS[%]"] = $["FLUID_YES_ANSWERS"] / $["FLUID_QUERIES"];
	$["CALL_SUMMARIZER_CACHE_MISSES[%]"] = $["CALL_SUMMARIZER_CACHE_MISSES"] / $["CALL_SUMMARIZER_APPLICATIONS"];
	$["LOOP_SUMMARIZER_CACHE_MISSES[%]"] = $["LOOP_SUMMARIZER_CACHE_MISSES"] / $["LOOP_SUMMARIZER_APPLICATIONS"];
'
mlr -I --csv put "$dsl" "$outfile"

# Fix values in case previous step computed .../0

sed -E -i 's/\b-?nan\b/0/g' "$outfile"

# Re-arranging columns (sort by header)

< "$outfile" \
sed '1s/^FILE,/ a &/;1s/OVERALL_TIME\[ms\],/ b &/' |
datamash -t, transpose |
LC_ALL=C sort |
sed '1,2s/^ . //g' |
datamash -t, transpose |
sponge "$outfile"

# Finish

cat "$outfile"
rm "$outfile"
