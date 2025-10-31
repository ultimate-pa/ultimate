#!/bin/bash
# Small script that is tailored to struebli
# After executing getunsounds.py to generate .set files, perform some postprocessing:
# - remove path prefixes with sed
# - merge new .set files with already existing ones
# - overwrite existing ones

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
SVCOMP=$(echo "$SCRIPT_DIR" | grep -oP "svcomp\d+")

merge(){
  f="$1"
  prefix=""
  if [ -n "$2" ] ; then prefix="$2_" ; fi
  oldset="/storage/repos/svcomp/c/""$prefix$f"
  cp "$f" "current_$f"
  f="current_$f"
  if [ ! -e "$oldset" ]; then
    echo "$oldset does not exist, no need to merge"
  else
    echo "Size of ${oldset}: $(wc -l "$oldset")"
    cat "$oldset" >> "$f"
    cat "$f" | sort | uniq >  tmp-"$f"
    mv tmp-"$f" "$f"
    echo "After merge:       $(wc -l "$f")"
  fi
  mv "$f" "$oldset"
}

for set_file in *unsound*set; do
  if [ ! -e "$set_file" ]; then
    echo "No unsound* files here, exiting"
    exit 1
  fi

  sed -i 's/..\/sv-benchmarks\/c\///g' "$set_file"

  merge "$set_file"
  merge "$set_file" "$SVCOMP"
done
