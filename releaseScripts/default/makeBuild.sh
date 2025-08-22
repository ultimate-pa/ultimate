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

# Default platforms for the build of Ultimate
PLATFORMS=("linux" "win32")
# Default initial heap memory size for Ultimate products
MEM_HEAP_INIT_SIZE="2M"
# Default maximum heap memory size for Ultimate products
MEM_HEAP_MAX_SIZE="4G"
# Default maximum stack memory size for Ultimate products
MEM_STACK_MAX_SIZE="1M"

_print_help() {
  printf 'Usage: %s [-i <size>] [-m <size>] [-s <size>] [-p all|linux|win32] [-h]\n' "${0}"
  print_newline
  printf 'Options:\n'
  printf '  -i    Set initial heap memory size for Ultimate products (default: %s)\n' "${MEM_HEAP_INIT_SIZE}"
  printf '  -m    Set maximum heap memory size for Ultimate products (default: %s)\n' "${MEM_HEAP_MAX_SIZE}"
  printf '  -s    Set maximum stack memory size for Ultimate products (default: %s)\n' "${MEM_STACK_MAX_SIZE}"
  printf '  -p    Specify platforms to build for:\n'
  printf '          all    build for Linux and Windows (default)\n'
  printf '          linux  build only for Linux\n'
  printf '          win32  build only for Windows\n'
  printf '  -h    Show this help message\n'
}

_validate_memory_size() {
  local MEM_OPT="${1}"
  local MEM_SIZE="${2}"

  # Check if memory size is valid (e.g., 512, 1024K, 2MB, 4GB, etc.)
  if [[ ! "${MEM_SIZE}" =~ ^[0-9]+[KMG]$ ]]; then
    printf '%s: invalid value for %s -- %s\n' "${0}" "${MEM_OPT}" "${MEM_SIZE}"
    print_newline
    _print_help
    exit 1
  fi
}

build_parseopts() {
  while getopts "i:m:s:p:h" OPT; do
    case "${OPT}" in
      i)
        _validate_memory_size "-i" "${OPTARG}"
        MEM_HEAP_INIT_SIZE="${OPTARG}"
        ;;
      m)
        _validate_memory_size "-m" "${OPTARG}"
        MEM_HEAP_MAX_SIZE="${OPTARG}"
        ;;
      s)
        _validate_memory_size "-s" "${OPTARG}"
        MEM_STACK_MAX_SIZE="${OPTARG}"
        ;;
      p)
        case "${OPTARG}" in
          all)
            # Use all platforms by default
            ;;
          linux)
            PLATFORMS=("linux")
            ;;
          windows)
            PLATFORMS=("win32")
            ;;
          *)
            printf '%s: invalid option for -p -- %s\n' "${0}" "${OPTARG}"
            print_newline
            _print_help
            exit 1
            ;;
        esac
        ;;
      h)
        print_newline
        _print_help
        exit 0
        ;;
      *)
        print_newline
        _print_help
        exit 1
        ;;
    esac
  done
}

build_init() {
  printf '▗▄▄▖ ▗▖ ▗▖▗▄▄▄▖▗▖   ▗▄▄▄ \n'
  printf '▐▌ ▐▌▐▌ ▐▌  █  ▐▌   ▐▌  █\n'
  printf '▐▛▀▚▖▐▌ ▐▌  █  ▐▌   ▐▌  █\n'
  printf '▐▙▄▞▘▝▚▄▞▘▗▄█▄▖▐▙▄▄▖▐▙▄▄▀\n'
  printf '┏━━━━━━━━━━━━━━━━━━━━━━━┓\n'
  printf '┃   Ultimate Products   ┃\n'
  printf '┗━━━━━━━━━━━━━━━━━━━━━━━┛\n'
  print_newline
}

build_check() {
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

build_run() {
  spushd "../../trunk/source/BA_MavenParentUltimate/"

  print_heading "Using the build tools"
  print_cmd_version "${VERS_MVN}" "               Maven"
  print_cmd_version "${VERS_JVM}" "        Java Runtime"
  print_cmd_version "${VERS_JDK}" "Java Development Kit"
  print_newline

  print_heading "Using the configuration for Ultimate"
  print_memory_size "${MEM_HEAP_INIT_SIZE}" "Initial heap  memory size"
  print_memory_size "${MEM_HEAP_MAX_SIZE}"  "Maximum heap  memory size"
  print_memory_size "${MEM_STACK_MAX_SIZE}" "Maximum stack memory size"
  print_newline

  print_heading "Start Ultimate build"
  exit_on_fail mvn -T 1C clean install -Pmaterialize
  print_newline

  spopd
}

build_package() {
  for PLATFORM in "${PLATFORMS[@]}"; do
    # makePackageConfig.sh <toolname> <launchername> <meminitheap> <memmaxheap> <memmaxstack> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
    print_heading "Package Ultimate Taipan [${PLATFORM}]"
    exit_on_fail bash makePackageConfig.sh "Taipan" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "AutomizerCInline_WitnessPrinter.xml" "NONE" "AutomizerCInline.xml" "AutomizerCInline_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate Automizer [${PLATFORM}]"
    exit_on_fail bash makePackageConfig.sh "Automizer" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "AutomizerCInline_WitnessPrinter.xml" "BuchiAutomizerCInline_WitnessPrinter.xml" "AutomizerCInline_IcfgBuilder.xml" "AutomizerCInline_WitnessPrinter.xml" "LTLAutomizerC.xml" "BuchiAutomizerCInline.xml"
    print_newline

    print_heading "Package Ultimate Kojak [${PLATFORM}]"
    exit_on_fail bash makePackageConfig.sh "Kojak" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "KojakC_WitnessPrinter.xml" "NONE" "NONE" "KojakC_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate GemCutter [${PLATFORM}]"
    exit_on_fail bash makePackageConfig.sh "GemCutter" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "AutomizerCInline_WitnessPrinter.xml" "NONE" "AutomizerCInline.xml" "AutomizerCInline_WitnessPrinter.xml" "NONE" "NONE"
    print_newline

    print_heading "Package Ultimate Referee [${PLATFORM}]"
    exit_on_fail bash makePackageConfig.sh "Referee" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "RefereeCInline.xml" "NONE" "RefereeCInline_IcfgBuilder.xml" "NONE" "NONE" "NONE"
    print_newline

    # makePackageSmall.sh <toolname> <launchername> <meminitheap> <memmaxheap> <memmaxstack> <targetarch>
    print_heading "Package Ultimate Command Line [${PLATFORM}]"
    exit_on_fail bash makePackageSmall.sh "CLI-E4" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}"
    print_newline

    print_heading "Package Ultimate Debug UI [${PLATFORM}]"
    exit_on_fail bash makePackageSmall.sh "Debug-E4" "UltimateDebug" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}"
    print_newline

    print_heading "Package Ultimate DeltaDebugger [${PLATFORM}]"
    exit_on_fail bash makePackageSmall.sh "DeltaDebugger" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}"
    print_newline

    print_heading "Package Ultimate Eliminator [${PLATFORM}]"
    exit_on_fail bash makePackageSmall.sh "Eliminator" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}"
    print_newline

    print_heading "Package Ultimate WebBackend [${PLATFORM}]"
    exit_on_fail bash makePackageSmall.sh "WebBackend" "WebBackend" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}"
    print_newline

    # makePackageReqCheck.sh <toolname> <launchername> <meminitheap> <memmaxheap> <memmaxstack> <targetarch> <reqchecktc> <testgentc>
    print_heading "Package Ultimate ReqCheck [${PLATFORM}]"
    exit_on_fail bash makePackageReqCheck.sh "ReqCheck" "Ultimate" "${MEM_HEAP_INIT_SIZE}" "${MEM_HEAP_MAX_SIZE}" "${MEM_STACK_MAX_SIZE}" "${PLATFORM}" "ReqCheck.xml" "ReqCheck.xml"
    print_newline
  done
}

build_parseopts "${@}"
build_init
build_check
build_run
build_package
