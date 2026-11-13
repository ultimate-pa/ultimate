#!/bin/bash
#-------------------------------------------------------------------------------
# This script generates a ZIP archive for an Ultimate product that should be
# deployed.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Start the actual script
if [ "${#}" -le 2 ]; then
  echo "Not enough arguments supplied -- use arguments in the following order"
  echo "1. the toolname"
  echo "2. 'linux', 'macosx' or 'win32' for the operating system"
  echo "3. 'x86_64' or 'aarch64' for the architecture"
  exit 1
fi

TOOLNAME="${1}"
if [ -z "${TOOLNAME}" ]; then
  echo "First argument (toolname) cannot be empty"
  exit 1
fi
LCTOOLNAME="$(echo "${TOOLNAME}" | tr '[A-Z]' '[a-z]')"
echo "Using ${TOOLNAME} (${LCTOOLNAME}) as toolname"

if [ -z "${3}" ]; then
  echo "Third argument (architecture) cannot be empty"
  exit 1
fi

# Architecture-specific variables
if [ "${2}" == "linux" ]; then
  echo "Building .zip for linux ..."
  OS="linux"
elif [ "${2}" == "macosx" ]; then
  echo "Building .zip for macosx ..."
  OS="macosx"
elif [ "${2}" == "win32" ]; then
  echo "Building .zip for win32 ..."
  OS="win32"
else
  echo "Wrong argument: ""${2}"" -- use 'linux', 'macosx' or 'win32'"
  exit 1
fi

ARCH="${3}"
case "${ARCH}" in
  x86_64|aarch64) ;;
  *)
    echo "Wrong argument: ""${3}"" -- use 'x86_64' or 'aarch64' for the architecture"
    exit 1
    ;;
esac

TARGETDIR="U${TOOLNAME}-${OS}-${ARCH}"
ZIPFILE="Ultimate${TOOLNAME}-${OS}-${ARCH}.zip"

# Removing files and dirs from previous deployments
if [ -f "${ZIPFILE}" ]; then
  echo "Removing old ${ZIPFILE} file"
  rm "${ZIPFILE}"
fi

# Creating ZIP archive
echo "Creating ${ZIPFILE} archive"
exit_on_fail zip -q "${ZIPFILE}" -r "${TARGETDIR}"/*
