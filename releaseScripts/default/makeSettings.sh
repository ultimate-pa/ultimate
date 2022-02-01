#!/bin/bash
# This file contains shared functions and settings for the make*.sh tools used by Ultimate. 
# In particular, it defines all Ultimate tools that can be deployed 

### Shared functions 
function test {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        echo "$@ failed with $1"
        exit $status
    fi
    return $status
}

function copy_if_non_empty {
    local source="$1"
    local target="$2"
    if [ ! -z "$source" ]; then 
        test cp "$source" "$target"
    fi
}

function exitOnFail {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with $1"
		exit $status
    fi
    return $status
}

function abort {
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

function test_if_cmd_is_available {
  local cmd_path=`command -v "$@"`
  [ $? -eq 0 ] || { echo >&2 "I require $@ but it's not installed. Aborting."; exit 1; }
  if ! [[ -f "$cmd_path" && -x $(realpath "$cmd_path") ]]; then
    echo >&2 "I require $@ but it's not executable. Aborting."; exit 1;
  fi
}

### Shared settings 


