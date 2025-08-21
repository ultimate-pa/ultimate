#!/bin/bash
#-------------------------------------------------------------------------------
# This script builds Ultimate with Maven and then creates deployable zip archives for all tools.
# Note that it does no longer build the website, as this requires Ruby and Jekyll.
# If you want to build the website, use makeWebsite.sh after makeFresh.sh.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"

# Load and execute all Ultimate build steps before archive function is called.
source "${DIR}/makeBuild.sh"

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
  for PLATFORM in "${PLATFORMS[@]}"; do
    # makeZip.sh <toolname> <targetarch>
    print_heading "Archive Ultimate Taipan [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Taipan" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Automizer [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Automizer" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Kojak [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Kojak" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate GemCutter [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "GemCutter" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Referee [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Referee" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate DeltaDebugger [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "DeltaDebugger" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Eliminator [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Eliminator" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate WebBackend [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "WebBackend" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate ReqCheck [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "ReqCheck" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Command Line [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "CLI-E4" "${PLATFORM}"
    print_newline

    print_heading "Archive Ultimate Debug UI [${PLATFORM}]"
    exit_on_fail bash makeZip.sh "Debug-E4" "${PLATFORM}"
    print_newline
  done
}

archive_init
archive_run
