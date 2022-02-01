#!/bin/bash
# save file 

re='^[0-9]+$'
if ! [[ $2 =~ $re ]] ; then
   echo "error: $2 not a number" >&2
   exit 1
fi

csv_file="$1"/CsvTraceAbstractionBenchmarks*
if [ ! -f $csv_file ]; then
    echo "error: $csv_file not found!"
    exit 1 
fi

cp "$1"/CsvTraceAbstractionBenchmarks* pcsv.csv

if csvcut -c Settings pcsv.csv | grep -q "$3"; test ${PIPESTATUS[0]} -eq 0; then 
    echo "error: $3 is not a setting"
    echo "available settings:"
    csvcut -c Settings "pcsv.csv" | tail -n +2 | sort | uniq 
    exit 1 
fi

# remove crashed inputs 
# first, remove all unknowns 
csvgrep -i -c "Category" -m "UNKNOWN (" pcsv.csv | csvgrep -i -c "Category" -m "TIMEOUT (" > cpcsv.csv 
count=$(wc -l < pcsv.csv)
count=$(echo "1 + $count - "`wc -l < cpcsv.csv` | bc )
mv cpcsv.csv pcsv.csv 


# then, remove all files for which not every setting produced a csv 
files=($(grep -oP "\\\[[:digit:]]+\..*?\.i(,|;)" pcsv.csv | sort | uniq))

for file in "${files[@]}"; do 
    filename=${file:1:${#file}-2}
    occurences=`grep -cP "${filename}(,|;)" pcsv.csv`
    if ((occurences % "$2")) ; then
        count=$((count+occurences))
        sed -i "/$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')/d" pcsv.csv
    fi
done 
echo "removed $count benchmark runs"

# remove [] 
perl -pi -e 's|\[(.*?)\]|\1|g' pcsv.csv

# remove paths from settings
perl -pi -e 's|F:\\repos\\ultimate\\trunk\\examples\\settings\\||g' pcsv.csv
perl -pi -e 's|F:\\repos\\ultimate\\trunk\\examples\\toolchains\\||g' pcsv.csv
perl -pi -e 's|regression-verif\\||g' pcsv.csv

# all file is ready 
cp pcsv.csv all.csv
cp pcsv.csv all-but-first.csv
cp pcsv.csv only-first.csv

# only first revisions is all where there is no .ats file as input and the setting is lazy 
first_revisions=($(csvgrep -c Settings -m "$3" pcsv.csv |  csvcut -c File | tail -n +2 | grep -v ".ats" | sort | uniq))
for file in "${first_revisions[@]}"; do 
    filename=$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')
    sed -i "/$filename\(,\|;\)/d" all-but-first.csv
done 

#not first revision is similar but collects all files where there is an entry with .ats 
not_first_revisions=($(csvgrep -c Settings -m "$3" pcsv.csv |  csvcut -c File | tail -n +2 | grep ".ats" | grep -oP ".*;" | sort | uniq))
for file in "${not_first_revisions[@]}"; do 
    file=${file:0:${#file}-1}
    sed -i "/$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')/d" only-first.csv
done 

 
# remove .ats inputs from all 
perl -pi -e 's|;.*?\.ats||g' all.csv
perl -pi -e 's|;.*?\.ats||g' all-but-first.csv

settings=($(csvcut -c Settings "pcsv.csv" | tail -n +2 | sort | uniq ))
# print overview 
for j in "all.csv" "all-but-first.csv" "only-first.csv"; do
    echo "$j"
    for i in "${settings[@]}"; do
        echo "$i"
        csvgrep -c3 -m "$i" "$j" | csvcut -c OverallTime | csvstat
    done
done


exit

