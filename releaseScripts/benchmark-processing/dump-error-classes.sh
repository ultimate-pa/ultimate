#!/bin/bash
# Small script that takes one argument and then checks the default results directory of Automizer for log files that contain that argument.
# Each log file is then re-run with arguments s.t. all smt scripts are dumped into a dump_<id>_<filename> folder

filename=$(echo "$1" | sed 's/ /_/g' | sed 's/:/_/g')
if [ ! -f "$filename" ] ; then 
  echo "$1" > "$filename"
  ack -l "$1" /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/results/ | xargs -d '\n' head -n 1 | grep java >> "$filename"
  sed -i 's/..\/..\/..\/trunk/\/storage\/repos\/ultimate\/trunk/g' "$filename"
fi 
k=0
tail -n 1 "$filename" | while IFS= read -r in; do
  k=$((k+1))
  dump="dump_${k}_${filename}"
  if [ -d "dump" ] ; then 
    echo "$dump already exists"
    continue
  fi
  echo "Dumping to $dump"
  mkdir "$dump"
  in+=" --rcfgbuilder.dump.smt.script.to.file true --rcfgbuilder.to.the.following.directory \"${dump}\" --traceabstraction.dump.smt.script.to.file true --traceabstraction.to.the.following.directory \"${dump}\""
  ${in}
done
