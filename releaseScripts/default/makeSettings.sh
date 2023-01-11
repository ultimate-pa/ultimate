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

### Shared settings 


