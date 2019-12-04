#!/bin/bash
# Small script that is tailored to struebli 
# After executing getunsounds.py to generate .set files, perform some postprocessing: 
# - remove path prefixes with sed 
# - merge new .set files with already existing ones 
# - overwrite existing ones 

for f in unsounds-*; do
  if [ ! -e "$f" ]; then 
    echo "No unsound* files here, exiting"
    exit 1
  fi
  
  sed -i 's/..\/sv-benchmarks\/c\///g' "$f"

  oldset="/storage/repos/svcomp/c/""$f"
  if [ ! -e "$oldset" ]; then 
    echo "$oldset does not exist, no need to merge"
  else
    echo "Size of ${oldset}: "$(wc -l "$oldset")
    cat "$oldset" >> "$f"
    cat "$f" | sort | uniq >  tmp-"$f"
    mv tmp-"$f" "$f"
    echo "After merge:       "$(wc -l "$f")
  fi
  mv "$f" /storage/repos/svcomp/c/
done
