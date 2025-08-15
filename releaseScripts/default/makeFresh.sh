#!/bin/bash
#-------------------------------------------------------------------------------
# This script builds Ultimate products with Maven and then creates deployable
# ZIP archives for the Ultimate products.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Load and execute all Ultimate build steps before archive function is called.
source "${DIR}/makePackage.sh"

archive_init() {
  printf ' ▗▄▖ ▗▄▄▖  ▗▄▄▖▗▖ ▗▖▗▄▄▄▖▗▖  ▗▖▗▄▄▄▖\n'
  printf '▐▌ ▐▌▐▌ ▐▌▐▌   ▐▌ ▐▌  █  ▐▌  ▐▌▐▌   \n'
  printf '▐▛▀▜▌▐▛▀▚▖▐▌   ▐▛▀▜▌  █  ▐▌  ▐▌▐▛▀▀▘\n'
  printf '▐▌ ▐▌▐▌ ▐▌▝▚▄▄▖▐▌ ▐▌▗▄█▄▖ ▝▚▞▘ ▐▙▄▄▖\n'
  printf '┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓\n'
  printf '┃        Ultimate Products         ┃\n'
  printf '┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛\n'
  print_newline
}

archive_run() {
  for TOOLNAME in "${PRODUCTS[@]}"; do
    for OS in "${OSS[@]}"; do
      # makeZip.sh <toolname> <os>
      print_heading "Archive Ultimate ${TOOLNAME} [${OS} | ${ARCH}]"
      exit_on_fail bash makeZip.sh "${TOOLNAME}" "${OS}"
      print_newline
    done
  done
}

archive_init
archive_run
