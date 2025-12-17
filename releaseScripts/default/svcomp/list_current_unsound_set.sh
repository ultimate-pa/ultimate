#!/bin/bash
filter="$1"
if [ -z "$filter" ] ; then
  filter=".*"
fi

sep=""
while IFS= read -r l ; do
  l=${l#\"}
  l=${l%\"}
  echo -e "$sep## $l"
  curl -sL "$l"
  sep="\n"
done < <(curl -sL "https://struebli.informatik.uni-freiburg.de/svcomp/c/" | grep -oP "href=\"\K.*unsound.*set\"" | grep -E "$filter" | sed -E 's;(.*);"https://struebli.informatik.uni-freiburg.de/svcomp/c/\1;g')

## not inside the script: 
# curl -sL "https://struebli.informatik.uni-freiburg.de/svcomp/c/" | grep -oP "href=\"\K.*unsound.*set\"" | sed -E 's;(.*);"https://struebli.informatik.uni-freiburg.de/svcomp/c/\1;g' | grep "automizer" | xargs sh -c 'for arg do echo -e "\n## $arg" ; curl -sL "$arg" ; done' _