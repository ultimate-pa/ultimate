#!/bin/bash
# Small script that takes a file containing all Ultimate calls that were unsound and produces a benchexec .xml file from it 


input="${1}" 
svcomp_dir="/storage/repos/svcomp"
properties_dir="${svcomp_dir}/c/properties"
TIMESTAMP=`date +%m-%d-%Y-%H-%M`
outfile="svcomp19-unsound-${TIMESTAMP}.xml"

# normalize the file 
echo "Normalizing $input ..."
sed 's/..\/..\/sv-benchmarks\/c\/Systems_DeviceDriversLinux64_ReachSafety.prp/..\/..\/sv-benchmarks\/c\/properties\/unreach-call.prp/g' $input | \
sed 's/..\/..\/sv-benchmarks\/c\/ReachSafety.prp/..\/..\/sv-benchmarks\/c\/properties\/unreach-call.prp/g' | \
sed 's/..\/..\/sv-benchmarks\/c\/MemSafety.prp/..\/..\/sv-benchmarks\/c\/properties\/valid-memsafety.prp/g'| \
sed 's/..\/..\/sv-benchmarks/\/storage\/repos\/svcomp/g' | \
sed 's/ --full-output//g' | \
sed 's/.\/Ultimate.py --spec //g' | \
sed 's/ --file//g' > tmp-file  


echo '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>' > "$outfile" 
echo '<benchmark tool="ultimateautomizer" memlimit="16GB" timelimit="1800" hardtimelimit="1800" cpuCores="4">' >> "$outfile" 
echo '    <rundefinition name="sv-comp19-unsound"></rundefinition>' >> "$outfile" 
echo '    <option name="--full-output"/>' >> "$outfile" 
echo '' >> "$outfile" 


for j in `grep -oP '.*/\K.+\.prp' tmp-file | sort | uniq` ; do 
    for i in {'32bit','64bit'}; do 
        echo "Writing block for $i $j"
        # write tasks block 
        printf '    <tasks name="' >> "$outfile"
        printf "${j}-${i}" >> "$outfile"
        printf '">\n' >> "$outfile"
        
        # write include files 
        grep "$i" tmp-file | grep "$j" | sort | uniq | sed 's/ --architecture.*//g' | sed 's/.*\.prp //g' | sed 's/\(.*\)/        <include>\1<\/include>/g' >> "$outfile" 

        # write property file 
        printf '        <propertyfile>' >> "$outfile" 
        printf "${properties_dir}/$j" >> "$outfile" 
        printf '</propertyfile>\n' >> "$outfile" 
        
        # write architecture option 
        printf '        <option name="--architecture">' >> "$outfile" 
        printf "$i" >> "$outfile" 
        printf '</option>\n' >> "$outfile" 
        
        #close tasks 
        printf '    </tasks>\n\n' >> "$outfile"
    done 
done 

echo '' >> "$outfile" 
echo '</benchmark>' >> "$outfile" 
rm tmp-file

