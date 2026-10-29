#!/bin/bash
#-------------------------------------------------------------------------------
# This script packages the selected Ultimate products in local folders.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"
source "${DIR}/makeProducts.sh"

# Load and execute all Ultimate build steps before package function is called.
source "${DIR}/makeBuild.sh"

package_run() {
  for TOOLNAME in "${PRODUCTS[@]}"; do
    for OS in "${OSS[@]}"; do
      print_heading "Package Ultimate ${TOOLNAME} [${OS} | ${ARCH}]"
      exit_on_fail package_product "${TOOLNAME}" "${OS}"
      print_newline
    done
  done
}

package_run
