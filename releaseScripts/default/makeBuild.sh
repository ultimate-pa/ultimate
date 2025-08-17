#!/bin/bash
#-------------------------------------------------------------------------------
# This script builds Ultimate with Maven and then creates all tools.
# Note that it does no longer build the website, as this requires Ruby and Jekyll.
# If you want to build the website, use 'makeWebsite.sh' after 'makeBuild.sh'.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"
source "${DIR}/semver2.sh"

start() {
  printf '▗▄▄▖ ▗▖ ▗▖▗▄▄▄▖▗▖   ▗▄▄▄ \n'
  printf '▐▌ ▐▌▐▌ ▐▌  █  ▐▌   ▐▌  █\n'
  printf '▐▛▀▚▖▐▌ ▐▌  █  ▐▌   ▐▌  █\n'
  printf '▐▙▄▞▘▝▚▄▞▘▗▄█▄▖▐▙▄▄▖▐▙▄▄▀\n'
  printf '┏━━━━━━━━━━━━━━━━━━━━━━━┓\n'
  printf '┃   Ultimate Products   ┃\n'
  printf '┗━━━━━━━━━━━━━━━━━━━━━━━┛\n'
  print_newline
}

check() {
  # Check if build tools are installed
  test_if_cmd_is_available   mvn
  test_if_cmd_is_available  java
  test_if_cmd_is_available javac
  # Retrieve build tool versions
  VERS_MVN="$(get_cmd_version   mvn --version)"
  VERS_JVM="$(get_cmd_version  java --version)"
  VERS_JDK="$(get_cmd_version javac --version)"
  # Check version of installed build tools
  test_cmd_version_greater_equal "${VERS_MVN}"  "3.9" "Maven"
  test_cmd_version_greater_equal "${VERS_JVM}" "21.0" "Java Runtime"
  test_cmd_version_greater_equal "${VERS_JDK}" "21.0" "Java Development Kit"
}

build() {
  spushd "../../trunk/source/BA_MavenParentUltimate/"

  print_heading "Using the build tools"
  print_cmd_version "${VERS_MVN}" "               Maven"
  print_cmd_version "${VERS_JVM}" "        Java Runtime"
  print_cmd_version "${VERS_JDK}" "Java Development Kit"
  print_newline

  print_heading "Start Ultimate build"
  exit_on_fail mvn -T 1C clean install -Pmaterialize
  print_newline

  spopd
}

package() {
  for platform in {linux,win32}; do
    # makePackageConfig.sh <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
    print_heading "Package Ultimate Taipan [${platform}]"
    exit_on_fail bash makePackageConfig.sh "Taipan" "${platform}" "AutomizerCInline_WitnessPrinter.xml" "NONE" "AutomizerCInline.xml" "AutomizerCInline_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate Automizer [${platform}]"
    exit_on_fail bash makePackageConfig.sh "Automizer" "${platform}" "AutomizerCInline_WitnessPrinter.xml" "BuchiAutomizerCInline_WitnessPrinter.xml" "AutomizerCInline_IcfgBuilder.xml" "AutomizerCInline_WitnessPrinter.xml" "LTLAutomizerC.xml" "BuchiAutomizerCInline.xml"
    print_newline

    print_heading "Package Ultimate Kojak [${platform}]"
    exit_on_fail bash makePackageConfig.sh "Kojak" "${platform}" "KojakC_WitnessPrinter.xml" "NONE" "NONE" "KojakC_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate GemCutter [${platform}]"
    exit_on_fail bash makePackageConfig.sh "GemCutter" "${platform}" "AutomizerCInline_WitnessPrinter.xml" "NONE" "AutomizerCInline.xml" "AutomizerCInline_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate Referee [${platform}]"
    exit_on_fail bash makePackageConfig.sh "Referee" "${platform}" "RefereeCInline.xml" "NONE" "RefereeCInline_IcfgBuilder.xml" "NONE" "NONE" "NONE"
    print_newline

    # makePackageSmall.sh <toolname> <targetarch>
    print_heading "Package Ultimate DeltaDebugger [${platform}]"
    exit_on_fail bash makePackageSmall.sh "DeltaDebugger" "${platform}"
    print_newline

    print_heading "Package Ultimate Eliminator [${platform}]"
    exit_on_fail bash makePackageSmall.sh "Eliminator" "${platform}"
    print_newline

    print_heading "Package Ultimate WebBackend [${platform}]"
    exit_on_fail bash makePackageSmall.sh "WebBackend" "${platform}"
    print_newline

    # makePackageReqCheck.sh <toolname> <targetarch> <reqchecktc> <testgentc>
    print_heading "Package Ultimate ReqCheck [${platform}]"
    exit_on_fail bash makePackageReqCheck.sh "ReqCheck" "${platform}" "ReqCheck.xml" "ReqCheck.xml"
    print_newline
  done
}

start
check
build
package
