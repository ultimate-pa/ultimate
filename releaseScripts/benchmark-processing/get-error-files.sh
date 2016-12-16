#/bin/bash
TOOLNAME=$2
ack -lQ "$1" tmp* | while read -r line ; do
        if [ ! -z "$line" ]; then
            FILE="examples/svcomp/"`grep -oE "*.\-i .* \-s " "$line" | cut -d ' ' -f 3 | cut -d '/' -f 5-`
			SETTING="svcomp2017/"$TOOLNAME"/"`grep -oE "*.\-s.*\.epf" "$line" | cut -d ' ' -f 3 | cut -d '/' -f 8-`
			TOOLCHAIN=`grep -oE "*.\-tc.*\.epf" "$line" | cut -d ' ' -f 3 | cut -d '/' -f 2-`
			echo "new Triple<>(\"$TOOLCHAIN\", \"$SETTING\", \"$FILE\"),"
        fi
done 

