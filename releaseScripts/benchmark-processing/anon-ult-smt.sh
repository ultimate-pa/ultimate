#!/bin/bash
# Replace variables named like |...| with sequential Strings from the latin alphabet

num2char() {
  	local list=( $(echo {A..Z} ))
# Returns a letter string: a-z
# Or: aa-az ba-bz, etc
	num=$1
	out=""
	if [[ $num -lt ${#list[@]} ]]
	then	out="${list[$num]}"
	else	high=$[ $num / ${#list[@]} ]
		out="${list[$high-1]}${list[$num - ($high * ${#list[@]})]}"
	fi
	echo "$out"
}


j=0
for i in `grep -oP '\|[^\| ]+\|' "$1" | sort | uniq | sed -e 's/[\/&]/\\&/g'` ; do
   c=`num2char $j`
   j=$((j+1))
   echo "Replacing $i with $c"
   sed -i "s/$i/$c/g" "$1"
   echo "(declare $c ...)" >> "$1"
 done

