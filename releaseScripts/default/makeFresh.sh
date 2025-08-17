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

archive() {
  for platform in {linux,win32}; do
    # makeZip.sh <toolname> <targetarch>
    print_heading "Archive Ultimate Taipan [${platform}]"
    exit_on_fail bash makeZip.sh "Taipan" "${platform}"
    print_newline

    print_heading "Archive Ultimate Automizer [${platform}]"
    exit_on_fail bash makeZip.sh "Automizer" "${platform}"
    print_newline

    print_heading "Archive Ultimate Kojak [${platform}]"
    exit_on_fail bash makeZip.sh "Kojak" "${platform}"
    print_newline

    print_heading "Archive Ultimate GemCutter [${platform}]"
    exit_on_fail bash makeZip.sh "GemCutter" "${platform}"
    print_newline

    print_heading "Archive Ultimate Referee [${platform}]"
    exit_on_fail bash makeZip.sh "Referee" "${platform}"
    print_newline

    print_heading "Archive Ultimate DeltaDebugger [${platform}]"
    exit_on_fail bash makeZip.sh "DeltaDebugger" "${platform}"
    print_newline

    print_heading "Archive Ultimate Eliminator [${platform}]"
    exit_on_fail bash makeZip.sh "Eliminator" "${platform}"
    print_newline

    print_heading "Archive Ultimate WebBackend [${platform}]"
    exit_on_fail bash makeZip.sh "WebBackend" "${platform}"
    print_newline

    print_heading "Archive Ultimate ReqCheck [${platform}]"
    exit_on_fail bash makeZip.sh "ReqCheck" "${platform}"
    print_newline
  done
}

archive
