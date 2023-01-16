#!/bin/bash 
# Tries to update SMTInterpol in Ultimate to the newest version 
# Execute it from a folder where SMTInterpol and Ultimate are both subfolders 

## Include the makeSettings shared functions 
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


make_diff(){
  spushd "$dir_smtinterpol"
  echo "Creating diff..."
  [ -e "$diff_file" ] && rm "$diff_file"
  [ -e "$changed_files" ] && rm "$changed_files"
  git diff "$smtinterpol_ver" -- SMTInterpol/src Library-SMTLIB/src Library-SMTLIBTest/src SMTInterpolTest/src SMTInterpolTest/test \
  ':(exclude,glob)**/util/datastructures/*' \
  ':(exclude,glob)**/util/HashUtils.java' \
  ':(exclude,glob)**/util/ScopeUtils.java' \
  ':(exclude,glob)**/build-parser.xml' \
  > "$diff_file"
  git diff --name-only "$smtinterpol_ver" -- SMTInterpol/src Library-SMTLIB/src Library-SMTLIBTest/src SMTInterpolTest/src SMTInterpolTest/test \
  ':(exclude,glob)**/util/datastructures/*' \
  ':(exclude,glob)**/util/HashUtils.java' \
  ':(exclude,glob)**/util/ScopeUtils.java' \
  ':(exclude,glob)**/build-parser.xml' \
  > "$changed_files"

  diff_file=$(readlink -f $diff_file)
  changed_files=$(readlink -f $changed_files)
  spopd
}

update_tools(){
  echo "Updating $dir_smtinterpol..."
  spushd "$dir_smtinterpol"
  exit_on_fail git checkout master
  exit_on_fail git fetch
  exit_on_fail git rebase
  exit_on_fail git clean -f -d
  echo "Building SMTInterpol..."
  exit_on_fail ant > /dev/null
  smtinterpol_cur=$(git describe --tags)
  spopd

  echo "Updating $dir_ultimate..."
  spushd "$dir_ultimate"
  smtinterpol_ver=$(grep -oP "VERSION\s*=\s*\"\K[0-9\.\-a-zA-Z]*" trunk/source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.java)
  spopd
}

get_versions() {
  echo "Normalizing versions..."
  smtinterpol_hash=$(echo "$smtinterpol_cur" | cut -d'-' -f 3)
  ultimate_hash=$(echo "$smtinterpol_ver" | cut -d'-' -f 3)
  smtinterpol_prehash=$(echo "$smtinterpol_cur" | cut -d'-' -f 1-2)
  ultimate_prehash=$(echo "$smtinterpol_ver" | cut -d'-' -f 1-2)
  smtinterpol_curnorm="$smtinterpol_prehash""-""${smtinterpol_hash:0:8}"
  smtinterpol_vernorm="$ultimate_prehash""-""${ultimate_hash:0:8}"

  echo "SMTInterpol version is $smtinterpol_cur (normalized: $smtinterpol_curnorm)"
  echo "Ultimate normalized is $smtinterpol_ver (normalized: $smtinterpol_vernorm)"
  smtinterpol_cur="$smtinterpol_curnorm"
  smtinterpol_ver="$smtinterpol_vernorm"

  if [ "$smtinterpol_ver" = "$smtinterpol_cur" ]; then 
    echo "No update necessary, version is already the latest ($smtinterpol_cur)"
    exit 0
  fi

  echo "Latest SMTInterpol version is $smtinterpol_cur, in Ultimate is $smtinterpol_ver, updating..."
}

patch_ultimate_manually(){
  echo "Problems applying the patch with git tools, just copying all changed files"
  while IFS= read -r file_name ; do
    source_file="${dir_smtinterpol}/${file_name}"
    target_file="${dir_ultimate}/trunk/source/${file_name}"
    target_dir=$(dirname "$target_file")
    if [ ! -f "$source_file" ] ; then
      exit_on_fail rm "$target_file"
      git rm "$target_file"
    else 
      exit_on_fail mkdir -p "$target_dir"
      exit_on_fail cp "$source_file" "$target_file"
      git add "$target_file"
    fi
  done < "$changed_files"
}

patch_ultimate(){
  spushd "$dir_ultimate"
  echo "Trying to apply patch..."
  ## first check, if nothing can be applied, do not update version
  if git apply --check --directory=trunk/source/ "$diff_file"; then
    echo "Using git to apply the patch"
    git apply --whitespace=nowarn --directory=trunk/source/ "$diff_file"
  else
    patch_ultimate_manually
  fi
  echo "Updating version"
  cp "$dir_smtinterpol"/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.java "$dir_ultimate"/trunk/source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.java
  git commit -a -m"Updated SMTInterpol to $smtinterpol_cur"
  spopd
}

function run() {
  repo_dir="${UPDATE_SMTINTERPOL_REPO_DIR:-"/mnt/crypto-storage/firefox"}"
  dir_smtinterpol="${UPDATE_SMTINTERPOL_SMTINTERPOL_DIR:-"${repo_dir}/smtinterpol"}"
  dir_ultimate="${UPDATE_SMTINTERPOL_ULTIMATE_DIR:-"${repo_dir}/ultimate"}"
  diff_file="smtinterpol.diff"
  changed_files="smtinterpol.changed"

  if [ ! -d "$dir_smtinterpol" ]; then 
    echo "Could not find directory $dir_smtinterpol"
    exit 1
  fi

  if [ ! -d "$dir_ultimate" ]; then 
    echo "Could not find directory $dir_ultimate"
    exit 1
  fi 

  update_tools
  get_versions
  make_diff
  patch_ultimate
}

run