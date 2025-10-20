#!/bin/bash
#-------------------------------------------------------------------------------
# This script generates a ZIP archive for an Ultimate product that should be deployed.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Start the actual script
if [ "${#}" -le 1 ]; then
  echo "Not enough arguments supplied -- use arguments in the following order"
  echo "1. the toolname"
  echo "2. 'linux' or 'win32' for the target platform"
  exit 1
fi

TOOLNAME="${1}"
if [ -z "${TOOLNAME}" ]; then
  echo "First argument (toolname) cannot be empty"
  exit 1
fi
LCTOOLNAME="$(echo "${TOOLNAME}" | tr '[A-Z]' '[a-z]')"
echo "Using ${TOOLNAME} (${LCTOOLNAME}) as toolname"

# Architecture-specific variables
if [ "${2}" == "linux" ]; then
  echo "Building .zip for linux..."
  ARCH="linux"
elif [ "${2}" == "win32" ]; then
  echo "Building .zip for win32..."
  ARCH="win32"
else
  echo "Wrong argument: ""${2}"" -- use 'linux' or 'win32'"
  exit 1
fi

TARGETDIR="U${TOOLNAME}-${ARCH}"
ZIPFILE="Ultimate${TOOLNAME}-${ARCH}.zip"

# Removing files and dirs from previous deployments
if [ -f "${ZIPFILE}" ]; then
  echo "Removing old ${ZIPFILE} file"
  rm "${ZIPFILE}"
fi

# Creating ZIP archive
echo "Creating ${ZIPFILE} archive"
exit_on_fail zip -q "${ZIPFILE}" -r "${TARGETDIR}"/*
