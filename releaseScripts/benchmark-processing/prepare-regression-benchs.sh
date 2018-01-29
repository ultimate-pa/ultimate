#!/bin/bash
# save file 
cp "$1"/CsvTraceAbstractionBenchmarks* pcsv.csv

# remove crashed inputs 

# find all individual files 
files=($(grep -oP "\\\[[:digit:]]+\..*?\.i(,|;)" pcsv.csv | sort | uniq))
count=0
for file in "${files[@]}"; do 
    filename=${file:1:${#file}-2}
    occurences=`grep -cP "${filename}(,|;)" pcsv.csv`
    if ((occurences % 3)) ; then
        count=$((count+occurences))
        sed -i "/$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')/d" pcsv.csv
        echo "Removing ${filename}"
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
first_revisions=($(csvgrep -c Settings -m "Lazy" pcsv.csv |  csvcut -c File | tail -n +2 | grep -v ".ats" | sort | uniq))
for file in "${first_revisions[@]}"; do 
    filename=$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')
    sed -i "/$filename\(,\|;\)/d" all-but-first.csv
done 

not_first_revisions=($(csvgrep -c Settings -m "Lazy" pcsv.csv |  csvcut -c File | tail -n +2 | grep ".ats" | grep -oP ".*;" | sort | uniq))
for file in "${not_first_revisions[@]}"; do 
    file=${file:0:${#file}-1}
    sed -i "/$(echo $file | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g')/d" only-first.csv
done 

 
# remove .ats inputs from all 
perl -pi -e 's|;.*?\.ats||g' all.csv
perl -pi -e 's|;.*?\.ats||g' all-but-first.csv

for j in "all.csv" "all-but-first.csv" "only-first.csv"; do 
    echo "$j"
    for i in "Lazy" "Eager" "Default.epf"; do 
        csvgrep -c3 -m "$i" "$j" | csvcut -c File,Settings,Result,OverallTime | csvstat
    done 
done 

exit

