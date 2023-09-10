#!/bin/bash
# Count benchmarks in a benchexec .xml file if it uses .set files

spushd() {
  pushd "$1" > /dev/null || { >&2 echo "Could not change into $1" ;  exit 1; }
}

spopd() {
  popd > /dev/null || { >&2 echo "Could not popd"; exit 1; }
}


for set in $(grep -oP ">\K.*?\.set" "$1") ; do
  if ! [ -f "$set" ] ; then >&2 echo "$set is not a file" ; exit 1 ; fi
  spushd "$(dirname "$set")"
  sset=$(basename "$set")
  while IFS= read -r line; do 
    if [[ $line == \#* ]] ; then continue ; fi
    for j in $line ; do 
      echo $j ; 
    done
  done < "$sset"
  spopd
done | wc -l
