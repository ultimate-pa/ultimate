#/bin/bash
while IFS='' read -r line || [[ -n "$line" ]]; do
	if [ ! -z "$line" ]; then 
		echo "Downloading "$line
		filename="${line##*/}"
		filename=`echo $filename  | rev | cut -d '.' -f 2- | rev` 
		wget -qO- $line | bunzip2 > $filename 
	fi 
done < "$1"
