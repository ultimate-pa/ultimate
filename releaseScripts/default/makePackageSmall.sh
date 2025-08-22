#!/bin/bash
#-------------------------------------------------------------------------------
# This script generates a package folder for an Ultimate product that should be deployed.
# It takes additional binaries from the adds/ folder. Currently, we use z3, cvc4 and mathsat.
# It also adds README, Ultimate.py, and various license files.
# It does not add toolchains or settings files, only the folder.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Start the actual script
if [ "${#}" -lt 6 ]; then
  echo "Not enough arguments supplied -- use arguments in the following order"
  echo "1. the toolname"
  echo "2. the launcher name"
  echo "3. the initial heap memory size"
  echo "4. the maximum heap memory size"
  echo "5. the maximum stack memory size"
  echo "6. 'linux' or 'win32' for the target platform"
  exit 1
fi

TOOLNAME="${1}"
if [ -z "${TOOLNAME}" ]; then
  echo "First argument (toolname) cannot be empty"
  exit 1
fi
LCTOOLNAME="$(echo "${TOOLNAME}" | tr '[A-Z]' '[a-z]')"
echo "Using ${TOOLNAME} (${LCTOOLNAME}) as toolname"

# Additional files for all architectures
ADDS=(
  "adds/LICENSE"
  "adds/LICENSE.GPL"
  "adds/LICENSE.GPL.LESSER"
  "adds/z3-LICENSE"
  "adds/cvc4-LICENSE"
  "adds/mathsat-LICENSE"
  "adds/ltl2ba-LICENSE"
  "adds/Ultimate.py"
  "adds/README"
)

# Architecture-specific variables
if [ "${6}" == "linux" ]; then
  echo "Packaging for linux..."
  ARCH="linux"
  ARCHPATH="products/${TOOLNAME}/linux/gtk/x86_64"
  ADDS+=("adds/z3" "adds/cvc4" "adds/mathsat" "adds/ltl2ba")
elif [ "${6}" == "win32" ]; then
  echo "Packaging for win32..."
  ARCH="win32"
  ARCHPATH="products/${TOOLNAME}/win32/win32/x86_64"
  ADDS+=("adds/z3.exe" "adds/cvc4.exe" "adds/mathsat.exe" "adds/mpir.dll" "adds/mathsat.dll" "adds/ltl2ba.exe")
else
  echo "Wrong argument: ""${6}"" -- use 'linux' or 'win32'"
  exit 1
fi

# Set version
VERSION="$(git rev-parse HEAD | cut -c1-8)"
echo "Version is ${VERSION}"

TARGETDIR="U${TOOLNAME}-${ARCH}"
CONFIGDIR="${TARGETDIR}"/config
DATADIR="${TARGETDIR}"/data

# Removing files and dirs from previous deployments
if [ -d "${TARGETDIR}" ]; then
  echo "Removing old ""${TARGETDIR}"
  rm -r "${TARGETDIR}"
fi

# Start copying files
echo "Copying files"
mkdir "${TARGETDIR}"
mkdir "${CONFIGDIR}"
mkdir "${DATADIR}"

exit_on_fail cp -a ../../trunk/source/BA_SiteRepository/target/"${ARCHPATH}"/* "${TARGETDIR}/"

# Copy all adds to target dir
for add in "${ADDS[@]}" ; do
  exit_on_fail cp "${add}" "${TARGETDIR}/"
done

setup_ultimate_product_info "${TARGETDIR}" "${2}" "${TOOLNAME}" "${VERSION}"
setup_ultimate_product_memory "${TARGETDIR}" "${2}" "${3}" "${4}" "${5}"
