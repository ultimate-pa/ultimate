#!/bin/bash
#-------------------------------------------------------------------------------
# This script generates a package folder for an Ultimate tool that should be deployed.
# It takes additional binaries from the adds/ folder. Currently, we use z3, cvc4 and mathsat.
# It also adds README, Ultimate.py, and various license files.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Start the actual script
if [ "${#}" -le 6 ]; then
  echo "Not enough arguments supplied -- use arguments in the following order"
  echo " 1. the toolname"
  echo " 2. the launcher name"
  echo " 3. the initial heap memory size"
  echo " 4. the maximum heap memory size"
  echo " 5. the maximum stack memory size"
  echo " 6. 'linux' or 'win32' for the target platform"
  echo " 7. (optional) the reach toolchain (e.g., 'AutomizerC_WitnessPrinter.xml')"
  echo " 8. (optional) the termination toolchain or NONE"
  echo " 9. (optional) the witness validation toolchain or NONE"
  echo "10. (optional) the memsafety deref and memtrack toolchain or NONE"
  echo "11. (optional) the ltl toolchain or NONE"
  echo "12. (optional) the termination witness validation toolchain or NONE"
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
  ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
  ADDS+=("adds/z3" "adds/cvc4" "adds/mathsat" "adds/ltl2ba")
elif [ "${6}" == "win32" ]; then
  echo "Packaging for win32..."
  ARCH="win32"
  ARCHPATH="products/CLI-E4/win32/win32/x86_64"
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
SETTINGS="../../trunk/examples/settings/default/${LCTOOLNAME}/*${TOOLNAME}*"

# Check all toolchain arguments
if [ -n "${7}" -a ! "NONE" = "${7}" ]; then
  TOOLCHAIN="../../trunk/examples/toolchains/${7}"
else
  echo "No reach toolchain specified, ommitting..."
  TOOLCHAIN=""
fi

if [ ! -z "${8}" -a ! "NONE" = "${8}" ]; then
  TERMTOOLCHAIN="../../trunk/examples/toolchains/${8}"
else
  echo "No termination toolchain specified, ommitting..."
  TERMTOOLCHAIN=""
fi

if [ ! -z "${9}" -a ! "NONE" = "${9}" ]; then
  VALTOOLCHAIN="../../trunk/examples/toolchains/${9}"
else
  echo "No witness validation toolchain specified, ommitting..."
  VALTOOLCHAIN=""
fi

if [ ! -z "${10}" -a ! "NONE" = "${10}" ]; then
  MEMDEREFMEMTRACKTOOLCHAIN="../../trunk/examples/toolchains/${10}"
else
  echo "No memory deref toolchain specified, ommitting..."
  MEMDEREFMEMTRACKTOOLCHAIN=""
fi

if [ ! -z "${11}" -a ! "NONE" = "${11}" ]; then
  LTLTOOLCHAIN="../../trunk/examples/toolchains/${11}"
else
  echo "No LTL toolchain specified, ommitting..."
  LTLTOOLCHAIN=""
fi

if [ ! -z "${12}" -a ! "NONE" = "${12}" ]; then
  TERMVALTOOLCHAIN="../../trunk/examples/toolchains/${12}"
else
  echo "No termination witness validation toolchain specified, ommitting..."
  TERMVALTOOLCHAIN=""
fi

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
copy_if_non_empty "${TOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}Reach.xml"
copy_if_non_empty "${TERMTOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}Termination.xml"
copy_if_non_empty "${VALTOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}ReachWitnessValidation.xml"
copy_if_non_empty "${MEMDEREFMEMTRACKTOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}MemDerefMemtrack.xml"
copy_if_non_empty "${LTLTOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}LTL.xml"
copy_if_non_empty "${TERMVALTOOLCHAIN}" "${CONFIGDIR}/${TOOLNAME}TerminationWitnessValidation.xml"
exit_on_fail cp ${SETTINGS} "${CONFIGDIR}/."

# Copy all adds to target dir
for add in "${ADDS[@]}" ; do
  exit_on_fail cp "${add}" "${TARGETDIR}/"
done

setup_ultimate_product_info "${TARGETDIR}" "${2}" "${TOOLNAME}" "${VERSION}"
setup_ultimate_product_memory "${TARGETDIR}" "${2}" "${3}" "${4}" "${5}"
