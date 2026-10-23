#!/bin/bash
#-------------------------------------------------------------------------------
# This script builds all Ultimate products with Maven.
#-------------------------------------------------------------------------------

# Load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "${DIR}" ]]; then DIR="${PWD}"; fi
source "${DIR}/makeSettings.sh"
source "${DIR}/makeProducts.sh"
source "${DIR}/semver2.sh"

# Default operating systems for the build of all Ultimate products
OSS=("linux" "win32")
# Default architecture for the build of all Ultimate products
ARCH="x86_64"
# Default selection of Ultimate products to build, package and archive;
# empty means all products (see build_parseopts)
PRODUCTS=()
# Default initial heap memory size for Ultimate products
MEM_HEAP_SIZE_INIT="2M"
# Default maximum heap memory size for Ultimate products
MEM_HEAP_SIZE_MAX="15G"
# Default maximum stack memory size for Ultimate products
MEM_STACK_SIZE_MAX="1M"

_print_help() {
  printf 'Usage: %s [-i <size>] [-m <size>] [-s <size>] [-o all|linux|win32] [-p <product>[,<product>...]|all] [-h]\n' "${0}"
  print_newline
  printf 'Options:\n'
  printf '  -i    Set initial heap  memory size for Ultimate products (default: %s)\n' "${MEM_HEAP_SIZE_INIT}"
  printf '  -m    Set maximum heap  memory size for Ultimate products (default: %s)\n' "${MEM_HEAP_SIZE_MAX}"
  printf '  -s    Set maximum stack memory size for Ultimate products (default: %s)\n' "${MEM_STACK_SIZE_MAX}"
  printf '  -o    Specify operating systems to build for:\n'
  printf '          all    build for Linux and Windows (default)\n'
  printf '          linux  build only for Linux\n'
  printf '          win32  build only for Windows\n'
  printf '  -p    Specify Ultimate products to build, package and archive:\n'
  printf '          all            use all products (default)\n'
  printf '          <product>...   comma-separated list of products, e.g. Taipan,Automizer;\n'
  printf '                         the option may be given multiple times\n'
  printf '          available products: %s\n' "${PRODUCTS_AVAILABLE[*]}"
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
  while getopts "i:m:s:p:o:h" OPT; do
    case "${OPT}" in
      i)
        _validate_memory_size "-i" "${OPTARG}"
        MEM_HEAP_SIZE_INIT="${OPTARG}"
        ;;
      m)
        _validate_memory_size "-m" "${OPTARG}"
        MEM_HEAP_SIZE_MAX="${OPTARG}"
        ;;
      s)
        _validate_memory_size "-s" "${OPTARG}"
        MEM_STACK_SIZE_MAX="${OPTARG}"
        ;;
      o)
        case "${OPTARG}" in
          all)
            # Use all platforms by default
            ;;
          linux)
            OSS=("linux")
            ;;
          win32)
            OSS=("win32")
            ;;
          *)
            printf '%s: invalid option for -o -- %s\n' "${0}" "${OPTARG}"
            print_newline
            _print_help
            exit 1
            ;;
        esac
        ;;
      p)
        if [ "${OPTARG}" == "all" ]; then
          PRODUCTS=("${PRODUCTS_AVAILABLE[@]}")
        else
          local SELECTED_PRODUCTS
          IFS=',' read -r -a SELECTED_PRODUCTS <<< "${OPTARG}"
          local SELECTED_PRODUCT
          for SELECTED_PRODUCT in "${SELECTED_PRODUCTS[@]}"; do
            if ! product_exists "${SELECTED_PRODUCT}"; then
              printf '%s: invalid option for -p -- %s\n' "${0}" "${SELECTED_PRODUCT}"
              print_newline
              _print_help
              exit 1
            fi
            # Avoid duplicates when the option is given multiple times
            local KNOWN_PRODUCT
            for KNOWN_PRODUCT in "${PRODUCTS[@]}"; do
              if [ "${KNOWN_PRODUCT}" == "${SELECTED_PRODUCT}" ]; then
                continue 2
              fi
            done
            PRODUCTS+=("${SELECTED_PRODUCT}")
          done
        fi
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
  # Use all products by default
  if [ "${#PRODUCTS[@]}" -eq 0 ]; then
    PRODUCTS=("${PRODUCTS_AVAILABLE[@]}")
  fi
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
  test_if_cmd_is_available mvn
  test_if_cmd_is_available java
  test_if_cmd_is_available javac
  # Retrieve build tool versions
  VERS_MVN="$(get_cmd_version mvn   --version)"
  VERS_JVM="$(get_cmd_version java  --version)"
  VERS_JDK="$(get_cmd_version javac --version)"
  # Check version of installed build tools
  test_cmd_version_greater_equal "${VERS_MVN}"  "3.9.9" "Maven"
  test_cmd_version_greater_equal "${VERS_JVM}" "21.0"   "Java Runtime"
  test_cmd_version_greater_equal "${VERS_JDK}" "21.0"   "Java Development Kit"
}

build_run() {
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

build_parseopts "${@}"
build_init
build_check
build_run
