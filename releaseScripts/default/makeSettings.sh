#!/bin/bash
# This file contains shared functions and settings for the make*.sh tools used by Ultimate. 
# In particular, it defines all Ultimate tools that can be deployed 

### Shared functions 
exit_on_fail() {
  "$@"
  local status=$?
  if [ $status -ne 0 ]; then
    echo "$* failed with exit code $status"
    exit $status
  fi
  return $status
}

copy_if_non_empty() {
  local source="$1"
  local target="$2"
  if [ -n "$source" ]; then 
    exit_on_fail cp "$source" "$target"
  fi
}

abort() {
  read -r -p "${1:-Are you sure? [y/N]} " response
  case "$response" in
      [yY][eE][sS]|[yY]) 
          false
          ;;
      *)
          true
          ;;
  esac
}

test_if_cmd_is_available() {
  local cmd_path
  if ! cmd_path=$(command -v "$@") ; then
    echo >&2 "I require $* but it's not installed. Aborting."
    exit 1
  fi
  if ! [[ -f "$cmd_path" && -x $(realpath "$cmd_path") ]]; then
    echo >&2 "I require $* but it's not executable. Aborting."
    exit 1
  fi
}

spushd() {
  pushd "$1" > /dev/null || { echo "Could not change into $1" ;  exit 1; }
}

spopd() {
  popd > /dev/null || { echo "Could not popd from $PWD"; exit 1; }
}

git_is_clean() {
  git diff-index --quiet "${1:-HEAD}" --
}

get_git_root() {
  if root_dir=$(git rev-parse --show-toplevel 2>/dev/null ) ; then
    echo "$root_dir"
  else
    echo "Not a .git directory: $PWD"
    exit 1
  fi
}

# move to root of current git directory, execute command
# abort if no git directory
run_in_git_root() {
  root_dir=$(get_git_root)
  spushd "$root_dir"
  "$@"
  spopd
}

is_ming() {
  uname | grep -q "MING"
}

is_linux() {
  [[ "$OSTYPE" == "linux-gnu"* ]]
}

is_macos() {
  [[ "$OSTYPE" == "darwin"* ]]
}

is_windows() {
  [[ "$OSTYPE" == "cygwin" ]] || [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "win32" ]]
}

run_python() {
  if is_windows ; then
    py -3 "$@"
  else
    python3 "$@"
  fi
}

# populate ULT_VERSION
get_ult_version(){
  spushd "$(get_git_root)/releaseScripts/default/UAutomizer-linux"
  ULT_VERSION=$(run_python Ultimate.py --ultversion)
  local rtr_code="$?"
  if ! [[ "$rtr_code" -eq "0" ]] ; then
    echo "./Ultimate.py --ultversion failed with $rtr_code"
    echo "Output was:"
    echo "$ULT_VERSION"
    exit $rtr_code
  fi
  ULT_VERSION=$(echo "$ULT_VERSION" | head -n 1 | sed 's/This is Ultimate //g ; s/origin.//g')
  if [ -z "$ULT_VERSION" ] ; then
    echo "Could not extract version string from './Ultimate.py --ultversion' output:"
    echo "$ULT_VERSION"
    exit 1
  fi
  spopd
}