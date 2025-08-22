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

test_cmd_version_greater_equal() {
  local CMD_VERS_ACTUAL="${1}"
  local CMD_VERS_EXPCTD="${2}"
  local CMD_NAME="${3}"

  if [ "$(semver_compare ${CMD_VERS_ACTUAL} ${CMD_VERS_EXPCTD})" -eq -1 ]; then
    printf '%s version %s is too old. ' "${CMD_NAME}" "${CMD_VERS_ACTUAL}"
    printf 'Please install %s %s or newer.\n' "${CMD_NAME}" "${CMD_VERS_EXPCTD}"
    exit 1
  fi
}

setup_ultimate_product_info() {
  local PRODUCT_PATH="${1}"
  local PRODUCT_LAUNCHER="${2}"
  local PRODUCT_NAME="${3}"
  local PRODUCT_VERSION="${4}"

  if [[ -f "${PRODUCT_PATH}/Ultimate.py" ]]; then
    echo "Setup version and toolname for Ultimate.py"
    # Replacing toolname value in Ultimate.py
    exit_on_fail sed -i "s/^toolname =.*$/toolname = \'${PRODUCT_NAME}\'/g" "${PRODUCT_PATH}/Ultimate.py"
    # Replacing version value in Ultimate.py
    exit_on_fail sed -i "s/^version =.*$/version = \'${PRODUCT_VERSION}\'/g" "${PRODUCT_PATH}/Ultimate.py"
    # Adjust permission to execute Ultimate.py
    exit_on_fail chmod a+x "${PRODUCT_PATH}/Ultimate.py"
  fi

  if [[ -f "${PRODUCT_PATH}/${PRODUCT_LAUNCHER}" ]]; then
    echo "Change permissions to run ${PRODUCT_LAUNCHER}"
    # Adjust permission to execute product launcher (e.g., 'Ultimate' launcher executable)
    exit_on_fail chmod a+x "${PRODUCT_PATH}/${PRODUCT_LAUNCHER}"
  fi
}

setup_ultimate_product_memory() {
  local PRODUCT_PATH="${1}"
  local PRODUCT_LAUNCHER="${2}"
  local PRODUCT_MEM_HEAP_MAX="${3}"
  local PRODUCT_MEM_STACK_MAX="${4}"

  if [[ -f "${PRODUCT_PATH}/${PRODUCT_LAUNCHER}.ini" ]]; then
    echo "Setup maximum stack and heap size for ${PRODUCT_LAUNCHER}"
    # Replacing maximum heap memory size in *.ini
    exit_on_fail sed -i "s/^-Xmx.*$/-Xmx${PRODUCT_MEM_HEAP_MAX}/g" "${PRODUCT_PATH}/${PRODUCT_LAUNCHER}.ini"
    # Replacing maximum stack memory size in *.ini
    exit_on_fail sed -i "s/^-Xms.*$/-Xms${PRODUCT_MEM_STACK_MAX}/g" "${PRODUCT_PATH}/${PRODUCT_LAUNCHER}.ini"
  fi

  if [[ -f "${PRODUCT_PATH}/Ultimate.py" ]]; then
    echo "Setup maximum stack and heap size in Ultimate.py"
    # Replacing maximum heap memory size in Ultimate.py
    exit_on_fail sed -i "s/^memory_heap_size_max =.*$/memory_heap_size_max = \'${PRODUCT_MEM_HEAP_MAX}\'/g" "${PRODUCT_PATH}/Ultimate.py"
    # Replacing maximum stack memory size in Ultimate.py
    exit_on_fail sed -i "s/^memory_stack_size_max =.*$/memory_stack_size_max = \'${PRODUCT_MEM_STACK_MAX}\'/g" "${PRODUCT_PATH}/Ultimate.py"
  fi
}

get_cmd_version() {
  ${@} | grep -m1 -Eo "([[:digit:]]+\.)+[[:digit:]]+"
}

print_cmd_version() {
  local CMD_VERS="${1}"
  local CMD_NAME="${2}"

  printf '%s: %s\n' "${CMD_NAME}" "${CMD_VERS}"
}

print_memory_size() {
  local MEM_SIZE="${1}"
  local MEM_NAME="${2}"

  printf '%s: %s\n' "${MEM_NAME}" "${MEM_SIZE}"
}

print_newline() {
  printf '\n'
}

print_heading() {
  local HEADING_NAME="${1}"
  local HEADING_LENGTH="${#HEADING_NAME}"
  local HEADING_UNDERLINE="$(printf '━%.0s' $(seq 1 ${HEADING_LENGTH}))"

  printf '%s\n' "${HEADING_NAME}"
  printf '%s\n' "${HEADING_UNDERLINE}"
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
    if is_ming ; then
      cygpath "$root_dir"
    else
      echo "$root_dir"
    fi    
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