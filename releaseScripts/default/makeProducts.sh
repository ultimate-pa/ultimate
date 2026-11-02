#!/bin/bash
#-------------------------------------------------------------------------------
# This file contains the registry of all Ultimate products that can be packaged
# and the generic packaging logic shared by the make*.sh tools.
#-------------------------------------------------------------------------------

# Available Ultimate products that can be built, packaged and archived
PRODUCTS_AVAILABLE=(
  "Automizer"
  "DebugUI"
  "DeltaDebugger"
  "Eliminator"
  "GemCutter"
  "Kojak"
  "Referee"
  "ReqCheck"
  "Taipan"
  "WebBackend"
)

# Check whether the given toolname is a known Ultimate product
product_exists() {
  local TOOLNAME="${1}"
  local KNOWN_PRODUCT
  for KNOWN_PRODUCT in "${PRODUCTS_AVAILABLE[@]}"; do
    if [ "${KNOWN_PRODUCT}" == "${TOOLNAME}" ]; then
      return 0
    fi
  done
  return 1
}

# Package the given Ultimate product for the given operating system ('linux' or
# 'win32') in a local folder U<toolname>-<os>.
package_product() {
  local TOOLNAME="${1}"
  local OS="${2}"

  local LC_TOOLNAME="$(echo "${TOOLNAME}" | tr '[A-Z]' '[a-z]')"
  echo "Using ${TOOLNAME} (${LC_TOOLNAME}) as toolname"

  # Architecture-specific variables
  local ARCH="x86_64"
  local WS
  if [ "${OS}" == "linux" ]; then
    WS="gtk"
  elif [ "${OS}" == "win32" ]; then
    WS="win32"
  else
    echo "Wrong argument: ""${OS}"" -- use 'linux' or 'win32'" >&2
    exit 1
  fi

  # Specification of the product to package
  local LAUNCHER PRODUCT_DIR TOOLCHAINS

  case "${TOOLNAME}" in
    Automizer)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "AutomizerCInline_WitnessPrinter.xml:AutomizerReach.xml"
        "BuchiAutomizerCInline_WitnessPrinter.xml:AutomizerTermination.xml"
        "AutomizerCInline.xml:AutomizerReachWitnessValidation.xml"
        "AutomizerCInline_WitnessPrinter.xml:AutomizerMemDerefMemtrack.xml"
        "LTLAutomizerC.xml:AutomizerLTL.xml"
        "BuchiAutomizerCInline.xml:AutomizerTerminationWitnessValidation.xml"
      )
      ;;
    DebugUI)
      LAUNCHER="UltimateDebug"
      PRODUCT_DIR="Debug-E4"
      TOOLCHAINS=()
      ;;
    DeltaDebugger)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="DeltaDebugger"
      TOOLCHAINS=()
      ;;
    Eliminator)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="Eliminator"
      TOOLCHAINS=()
      ;;
    GemCutter)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "AutomizerCInline_WitnessPrinter.xml:GemCutterReach.xml"
        "AutomizerCInline.xml:GemCutterReachWitnessValidation.xml"
        "AutomizerCInline_WitnessPrinter.xml:GemCutterMemDerefMemtrack.xml"
      )
      ;;
    Kojak)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "KojakC_WitnessPrinter.xml:KojakReach.xml"
        "KojakC.xml:KojakReachWitnessValidation.xml"
        "KojakC_WitnessPrinter.xml:KojakMemDerefMemtrack.xml"
      )
      ;;
    Referee)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "RefereeCInline.xml:RefereeReach.xml"
        "RefereeCInline.xml:RefereeReachWitnessValidation.xml"
      )
      ;;
    ReqCheck)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "ReqCheck.xml:ReqCheck.xml"
        "ReqCheck.xml:ReqToTest.xml"
      )
      ;;
    Taipan)
      LAUNCHER="Ultimate"
      PRODUCT_DIR="CLI-E4"
      TOOLCHAINS=(
        "AutomizerCInline_WitnessPrinter.xml:TaipanReach.xml"
        "AutomizerCInline.xml:TaipanReachWitnessValidation.xml"
        "AutomizerCInline_WitnessPrinter.xml:TaipanMemDerefMemtrack.xml"
      )
      ;;
    WebBackend)
      LAUNCHER="WebBackend"
      PRODUCT_DIR="WebBackend"
      TOOLCHAINS=()
      ;;
    *)
      echo "Unknown product: ${TOOLNAME}" >&2
      exit 1
      ;;
  esac

  # Additional files for all products
  local ADDS=(
    "adds/licenses/LICENSE"
    "adds/licenses/LICENSE.GPL"
    "adds/licenses/LICENSE.GPL.LESSER"
    "adds/README"
  )

  # Architecture-specific solvers with licenses for all products
  for SOLVER_FILE in $(find "adds/solvers/${OS}/${ARCH}" -maxdepth 1 -type f -executable ! -name '*.so' ! -name '*.so.*' ! -name '*.dll'); do
    # Filename without path or extension
    SOLVER_FILENAME="${SOLVER_FILE##*/}"
    SOLVER_NAME="${SOLVER_FILENAME%.*}"

    # Solver binaries
    ADDS+=("${SOLVER_FILE}")

    # Corresponding license
    LICENSE_FILE="adds/licenses/${SOLVER_NAME}-LICENSE"
    if [[ -f "${LICENSE_FILE}" ]]; then
      ADDS+=("${LICENSE_FILE}")
    else
      echo "License for solver ${SOLVER_NAME} missing" >&2
      exit 1
    fi
  done

  # Launcher-specific scripts for products
  if [ "${LAUNCHER}" == "Ultimate" ]; then
    # Ultimate wrapper script
    ADDS+=("adds/Ultimate.py")
    # Basic system test script
    ADDS+=("adds/examples")
    ADDS+=("adds/scripts/${OS}/"smoketest.*)
  fi

  # Set version
  local VERSION="$(git rev-parse HEAD | cut -c1-8)"
  echo "Version is ${VERSION}"

  local TARGET_SRC_DIR="../../trunk/source/BA_SiteRepository/target"
  local TOOLCHAINS_SRC_DIR="../../trunk/examples/toolchains"
  local SETTINGS_SRC_DIR="../../trunk/examples/settings/default/${LC_TOOLNAME}/*${TOOLNAME}*"
  local TARGET_DST_DIR="U${TOOLNAME}-${OS}"
  local CONFIG_DST_DIR="${TARGET_DST_DIR}/config"
  local DATA_DST_DIR="${TARGET_DST_DIR}/data"

  # Removing files and dirs from previous deployments
  if [ -d "${TARGET_DST_DIR}" ]; then
    echo "Removing old ""${TARGET_DST_DIR}"
    rm -r "${TARGET_DST_DIR}"
  fi

  # Start copying files
  echo "Copying files"
  mkdir "${TARGET_DST_DIR}"
  mkdir "${CONFIG_DST_DIR}"
  mkdir "${DATA_DST_DIR}"

  exit_on_fail cp -a "${TARGET_SRC_DIR}/products/${PRODUCT_DIR}/${OS}/${WS}/${ARCH}/"* "${TARGET_DST_DIR}/"

  # Copy all toolchains to the config dir
  local TOOLCHAIN TOOLCHAIN_SRC_FILE TOOLCHAIN_DST_FILE
  for TOOLCHAIN in "${TOOLCHAINS[@]}" ; do
    TOOLCHAIN_SRC_FILE="${TOOLCHAIN%%:*}"
    TOOLCHAIN_DST_FILE="${TOOLCHAIN#*:}"
    copy_if_non_empty "${TOOLCHAINS_SRC_DIR}/${TOOLCHAIN_SRC_FILE}" "${CONFIG_DST_DIR}/${TOOLCHAIN_DST_FILE}"
  done

  # Copy the default settings
  # Products without toolchains have no settings
  if [ "${#TOOLCHAINS[@]}" -gt 0 ]; then
    exit_on_fail cp ${SETTINGS_SRC_DIR} "${CONFIG_DST_DIR}/"
  fi

  # Copy all adds to target dir
  local ADD
  for ADD in "${ADDS[@]}" ; do
    exit_on_fail cp -r "${ADD}" "${TARGET_DST_DIR}/"
  done

  setup_ultimate_product_info "${TARGET_DST_DIR}" "${LAUNCHER}" "${TOOLNAME}" "${VERSION}"
  setup_ultimate_product_memory "${TARGET_DST_DIR}" "${LAUNCHER}" "${MEM_HEAP_SIZE_INIT}" "${MEM_HEAP_SIZE_MAX}" "${MEM_STACK_SIZE_MAX}"
}
