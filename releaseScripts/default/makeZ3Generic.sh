#!/bin/bash
#
# Creates statically linked versions of z3 from the repository using generic
# CFLAGS in order to allow for maximum compatibility with different
# architectures.
#
# The following targets can be selected and are built in a single run
# (default: all of them):
#   - linux-x86_64    Linux x86_64, native build
#   - linux-aarch64   Linux ARM64, cross-compiled with the GNU AArch64 toolchain
#   - windows-x86_64  Windows x86_64, cross-compiled with mingw-w64
#
# Every target is built in its own build folder (buildtemp-<target>) in the
# current directory. The built executables are copied into the output
# directory (default: <script dir>/adds/solvers), each into its suitable
# per-target subdirectory; the actual paths are printed at the end of the
# run.
#
# The z3 version to build can be selected with '-v|--version' (git tag or
# branch). By default, the latest z3 version is built; the latest version is
# pinned in the script via the PINNED_Z3 variable, which is updated
# automatically on every default run.
#
# For usage, see the -h flag.
#
# License: LGPLv3
#
# (C) 2017 Marius Greitschus, University of Freiburg
# (C) 2023 Daniel Dietsch, University of Freiburg

set -e

GIT_FETCH_URL="https://github.com/Z3Prover/z3.git"
# see https://en.wikipedia.org/wiki/X86-64#Microarchitecture_levels
X86_FLAGS="-O2 -march=x86-64 -mtune=generic -pipe"
# generic flags for AArch64: ARMv8-A is the baseline architecture of all
# ARM64 CPUs, -mtune=generic maximizes compatibility with different cores
AARCH64_FLAGS="-O2 -march=armv8-a -mtune=generic -pipe"

# finding available variables is tricky:
# - some can be displayed with cmake -LAH 
# - some can be found in CMakeLists.txt
# - some are in README-CMake.md
CMAKE_FLAGS=(
-DCMAKE_BUILD_TYPE=Release
-DZ3_BUILD_EXECUTABLE:BOOL=ON
-DZ3_BUILD_LIBZ3_MSVC_STATIC=ON
-DZ3_BUILD_TEST_EXECUTABLES=OFF
-DZ3_ENABLE_EXAMPLE_TARGETS=OFF
-DZ3_LINK_TIME_OPTIMIZATION=ON
-DZ3_SINGLE_THREADED:BOOL=OFF
-DZ3_USE_LIB_GMP=OFF
-DBUILD_SHARED_LIBS=OFF
-DZ3_BUILD_LIBZ3_SHARED=OFF
-DCMAKE_EXE_LINKER_FLAGS='-static -Wl,--whole-archive -Wl,--no-whole-archive'
# -DCMAKE_STATIC_LINKER_FLAGS='-static -Wl,--whole-archive -Wl,--no-whole-archive'
)

MINGW_PREFIX="x86_64-w64-mingw32"
# Cross toolchain prefix for AArch64 (Debian: gcc-aarch64-linux-gnu,
# Arch: aarch64-linux-gnu-gcc)
AARCH64_PREFIX="aarch64-linux-gnu"

# Pinned z3 version, used by the '--pinned' option. It is updated
# automatically to the latest version whenever the script runs in the
# default '--latest' mode. Release tags are stored without their 'z3-'
# prefix (e.g. '4.15.4' for the tag 'z3-4.15.4').
PINNED_Z3="4.15.4"

TARGET_LINUX_X86_64="linux-x86_64"
TARGET_LINUX_AARCH64="linux-aarch64"
TARGET_WINDOWS_X86_64="windows-x86_64"
ALL_TARGETS=("${TARGET_LINUX_X86_64}" "${TARGET_LINUX_AARCH64}" "${TARGET_WINDOWS_X86_64}")

SCRIPT_DIR="$(cd "$(dirname "${0}")" && pwd)"
SCRIPT_PATH="${SCRIPT_DIR}/$(basename "${0}")"
ROOT="$(pwd)"
trap 'cd "${ROOT}"' EXIT

WORKING_DIR="z3temp"
DEFAULT_WORKING=true
BUILD_DIR_PREFIX="buildtemp"
BUILD_DIR=""
OUT_DIR="${SCRIPT_DIR}/adds/solvers"
DEFAULT_OUT=true
NUMCPUS=$(grep -c '^processor' /proc/cpuinfo)
NUMCPUS=$((NUMCPUS + 1))
NOUPDATE=false
DONTREMOVE=false

# Targets to build; empty means all targets (see ALL_TARGETS)
SELECTED_TARGETS=()

# Version selection: 'latest' (default), 'pinned' or an explicit version
# (git tag or branch); set by the argument parsing.
Z3_VERSION_MODE="latest"
Z3_VERSION_REF=""

# Target specific settings, set by configure_target()
BIN=""
STRIP_CMD=""
TARGET_FLAGS=""
TOOLCHAIN=""
DEST_SUBDIR=""

print_help()
{
    echo "Usage: ${0} [options]"
    echo
    echo " Options:"
    echo "  -g|--git-dir z3-gitdir      Directory of z3 Git-checkout."
    echo "                              If no directory is specified, a new"
    echo "                              checkout will be performed into a"
    echo "                              temporary directory which will be"
    echo "                              removed when done, unless the --no-remove-temp"
    echo "                              option is specified."
    echo
    echo "  -t|--targets target-list    Comma-separated list of targets to build:"
    echo "                              linux-x86_64, linux-aarch64, windows-x86_64."
    echo "                              Default: all targets."
    echo "                              Cross compilation needs mingw-w64 (Windows)"
    echo "                              and gcc-aarch64-linux-gnu/g++-aarch64-linux-gnu"
    echo "                              (AArch64) installed."
    echo
    echo "  -o|--output-dir output-dir  Specifies the directory in which the built"
    echo "                              z3 executables are placed, each in its"
    echo "                              suitable per-target subdirectory"
    echo "                              (linux/x86_64, linux/aarch64, win32/x86_64)."
    echo "                              Default: ${OUT_DIR}"
    echo
    echo "  -v|--version version        Git tag or branch of z3 to build. The"
    echo "                              'z3-' prefix of a release tag"
    echo "                              (e.g. z3-4.15.4) may be omitted."
    echo "                              Default: the latest z3 version (git tag)."
    echo
    echo "  --latest                    Build the latest z3 version (default)."
    echo "                              Updates PINNED_Z3 in the script."
    echo
    echo "  --pinned                    Build the z3 version pinned as"
    echo "                              PINNED_Z3 in the script."
    echo
    echo "  -j|--jobs number            Defines the number of parallel jobs"
    echo "                              that should be used when compiling z3."
    echo "                              Default: Number of CPUs + 1 on the current"
    echo "                              system. Here: ${NUMCPUS}"
    echo
    echo "  -n|--no-pull                Do not update the repository to the newest"
    echo "                              version. This only works with the -g flag."
    echo
    echo "  --no-remove-temp            Do not remove temporary files and directories"
    echo "                              after z3 has been built."
    echo
    echo "  -h | --help                 Print this help."
}

print_setup()
{
    echo "Using the following setup:"
    echo -e "  Fetch-URL:\t\t\t${GIT_FETCH_URL}"
    echo -en "  git-dir:\t\t\t${WORKING_DIR}"
    if [ ${DEFAULT_WORKING} = true ]; then
        echo " (default)"
    else
        echo
    fi
    echo -en "  output-dir:\t\t\t${OUT_DIR}"
    if [ ${DEFAULT_OUT} = true ]; then
        echo " (default)"
    else
        echo
    fi
    echo -e "  Targets:\t\t\t${SELECTED_TARGETS[*]}"
    local version_desc
    case ${Z3_VERSION_MODE} in
        latest)
            version_desc="latest"
            ;;
        pinned)
            version_desc="pinned (${PINNED_Z3})"
            ;;
        version)
            version_desc="${Z3_VERSION_REF}"
            ;;
    esac
    echo -e "  Z3 version:\t\t\t${version_desc}"
    echo -e "  Additional parameters:\t${CMAKE_FLAGS[*]}"
    echo -e "  CFLAGS and CXXFLAGS:\t\t${X86_FLAGS} (x86_64 targets), ${AARCH64_FLAGS} (aarch64 target)"
    echo -e "  Number of parallel jobs:\t${NUMCPUS}"
    echo
}

configure_target()
{
    local target="$1"

    case ${target} in
        ${TARGET_LINUX_X86_64})
            BIN="z3"
            STRIP_CMD="strip"
            TARGET_FLAGS="${X86_FLAGS}"
            TOOLCHAIN=""
            DEST_SUBDIR="linux/x86_64"
            ;;
        ${TARGET_LINUX_AARCH64})
            BIN="z3"
            STRIP_CMD="${AARCH64_PREFIX}-strip"
            TARGET_FLAGS="${AARCH64_FLAGS}"
            TOOLCHAIN="aarch64"
            DEST_SUBDIR="linux/aarch64"
            for tool in gcc g++ strip; do
                if ! command -v "${AARCH64_PREFIX}-${tool}" &> /dev/null ; then
                    echo "Error: ${AARCH64_PREFIX}-${tool} not found. Is the AArch64 cross toolchain installed?"
                    exit 1
                fi
            done
            ;;
        ${TARGET_WINDOWS_X86_64})
            BIN="z3.exe"
            STRIP_CMD="${MINGW_PREFIX}-strip"
            TARGET_FLAGS="${X86_FLAGS}"
            TOOLCHAIN="mingw"
            DEST_SUBDIR="win32/x86_64"
            for tool in gcc g++ strip; do
                if ! command -v "${MINGW_PREFIX}-${tool}" &> /dev/null ; then
                    echo "Error: ${MINGW_PREFIX}-${tool} not found. Is mingw-w64 installed?"
                    exit 1
                fi
            done
            ;;
        *)
            echo "Error: Unknown target: ${target}"
            exit 1
            ;;
    esac
}

# Verifies that the toolchains of all selected targets are available before
# building anything.
check_tools()
{
    local target
    for target in "${SELECTED_TARGETS[@]}"; do
        configure_target "${target}"
    done
}

# Writes a CMake toolchain file for cross compiling with mingw-w64.
write_mingw_toolchain()
{
    local file="$1"

    cat > "${file}" <<EOF
set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

set(CMAKE_C_COMPILER   ${MINGW_PREFIX}-gcc)
set(CMAKE_CXX_COMPILER ${MINGW_PREFIX}-g++)
set(CMAKE_RC_COMPILER  ${MINGW_PREFIX}-windres)

set(CMAKE_FIND_ROOT_PATH /usr/${MINGW_PREFIX})
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
EOF
}

# Writes a CMake toolchain file for cross compiling with the GNU AArch64 toolchain.
write_aarch64_toolchain()
{
    local file="$1"

    cat > "${file}" <<EOF
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR aarch64)

set(CMAKE_C_COMPILER   ${AARCH64_PREFIX}-gcc)
set(CMAKE_CXX_COMPILER ${AARCH64_PREFIX}-g++)

set(CMAKE_FIND_ROOT_PATH /usr/${AARCH64_PREFIX})
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
EOF
}

# Resolves a version string to a git ref. Accepts tags, branches and bare
# release versions ('4.15.4' for the release tag 'z3-4.15.4').
resolve_version_ref()
{
    local ref="$1"

    if [ "${ref#z3-}" != "${ref}" ] \
        || git rev-parse -q --verify "${ref}^{commit}" > /dev/null 2>&1 ; then
        echo "${ref}"
        return
    fi

    if git rev-parse -q --verify "z3-${ref}^{commit}" > /dev/null 2>&1 ; then
        echo "z3-${ref}"
        return
    fi

    # unresolvable; select_version_z3 reports the error
    echo "${ref}"
}

# Rewrites the pinned z3 version in this script. This is safe while the
# script is running because sed -i replaces the file with a new inode.
update_pin()
{
    local version="$1"

    # store release tags without their 'z3-' prefix
    version="${version#z3-}"

    if [ "${version}" = "${PINNED_Z3}" ]; then
        return
    fi

    sed -i "s|^PINNED_Z3=.*$|PINNED_Z3=\"${version}\"|" "${SCRIPT_PATH}"
    echo "Updated PINNED_Z3 in the script to ${version}"
    PINNED_Z3="${version}"
}

# Selects and checks out the z3 version to build; must be called inside the
# z3 repository directory.
select_version_z3()
{
    local ref

    case ${Z3_VERSION_MODE} in
        latest)
            # newest release tag (z3-<version>), sorted by version; ignore
            # moving or experimental tags like 'Nightly'
            ref=$(git tag -l 'z3-*' | sort -V | tail -n 1)
            if [ -z "${ref}" ]; then
                ref=$(git describe --tags "$(git rev-list --tags --max-count=1)")
            fi
            echo "Using the latest z3 version: ${ref}"
            update_pin "${ref}"
            ;;
        pinned)
            if [ -z "${PINNED_Z3}" ]; then
                echo "Error: No z3 version pinned in the script (PINNED_Z3 is empty)."
                echo "       Run the script once with '--latest' to set the pin."
                exit 1
            fi
            ref=$(resolve_version_ref "${PINNED_Z3}")
            echo "Using the pinned z3 version: ${ref}"
            ;;
        version)
            ref=$(resolve_version_ref "${Z3_VERSION_REF}")
            echo "Using z3 version: ${ref}"
            ;;
        *)
            echo "Error: Unknown version mode: ${Z3_VERSION_MODE}"
            exit 1
            ;;
    esac

    if ! git rev-parse -q --verify "${ref}^{commit}" > /dev/null ; then
        echo "Error: z3 version '${ref}' not found in the repository."
        exit 1
    fi

    git checkout "${ref}"
}

checkout_z3()
{
    if [ ${DEFAULT_WORKING} = false ]; then
        return
    fi

    if [ -d "${WORKING_DIR}" ]; then
        echo "Error: The directory for the Git checkout \"${WORKING_DIR}\" already exists."
        echo "       Please remove the directory first or use the -g option."
        exit 1
    fi

    echo "Cloning z3 into ${WORKING_DIR} ..."

    mkdir "${WORKING_DIR}"
    cd "${WORKING_DIR}"
    git clone "${GIT_FETCH_URL}" .
    select_version_z3
    cd "${ROOT}"
}

update_z3()
{
    if [ ${DEFAULT_WORKING} = true ]; then
        return
    fi

    if [ ! -d "${WORKING_DIR}" ]; then
        echo "Error: z3 git directory ${WORKING_DIR} does not exist."
        exit 1
    fi

    cd "${WORKING_DIR}"

    if [ ${NOUPDATE} = true ]; then
        echo "Skipping update of the repository. Using current head: $(git rev-parse --short HEAD)"
        cd "${ROOT}"
        return
    fi

    echo "Updating z3 in ${WORKING_DIR} ..."

    git fetch --tags --prune origin
    select_version_z3

    # fast-forward a checked-out branch to its upstream
    if [ "$(git rev-parse --abbrev-ref HEAD)" != "HEAD" ]; then
        git pull --ff-only
    fi

    cd "${ROOT}"
}

version_z3()
{
    cd "${WORKING_DIR}"
    TAG=$(git describe --tags 2> /dev/null || echo "unknown")
    VERSION_HASH=$(git rev-parse --short HEAD)
    BRANCH=$(git rev-parse --abbrev-ref HEAD)
    cd "${ROOT}/${BUILD_DIR}"

    Z3_VERSION="${TAG}-${BRANCH}-${VERSION_HASH}"
    echo "z3 version is: ${Z3_VERSION}"
    echo "${Z3_VERSION}" > "VERSION.z3"
    cd "${ROOT}"
}

check_binary()
{
    if [ "${TOOLCHAIN}" = "mingw" ]; then
        # PE binary: list the DLLs it imports. For a fully static
        # build this should only be system DLLs (KERNEL32, msvcrt/ucrt, ...),
        # but no libstdc++-6.dll, libgcc_s_seh-1.dll or libwinpthread-1.dll.
        if command -v "${MINGW_PREFIX}-objdump" &> /dev/null ; then
            "${MINGW_PREFIX}-objdump" -p "${BIN}" | grep "DLL Name" || true
        else
            echo "No ${MINGW_PREFIX}-objdump available"
        fi
        return
    fi

    # check for dynamic vs static linking
    if command -v readelf &> /dev/null ; then
        readelf -d "${BIN}"
    elif command -v objdump &> /dev/null ; then
        objdump -p "${BIN}"
    else
        echo "No readelf or objdump available"
    fi

    if [ "${TOOLCHAIN}" = "aarch64" ]; then
        return
    fi

    # check which cpuflags are required
    if command -v ~/.cargo/bin/elfx86exts &> /dev/null ; then
        ~/.cargo/bin/elfx86exts "${BIN}"
    else
        echo "No elfx86exts available"
        echo "Install it by visiting https://github.com/pkgw/elfx86exts"
    fi
}

compile_z3()
{
    local target="$1"

    configure_target "${target}"
    BUILD_DIR="${BUILD_DIR_PREFIX}-${target}"

    echo "Building z3 for ${target} ..."
    if [ -d "${BUILD_DIR}" ]; then
        rm -rf "${BUILD_DIR}"
    fi
    mkdir "${BUILD_DIR}"
    cd "${BUILD_DIR}"

    export CFLAGS="${TARGET_FLAGS}"
    export CXXFLAGS="${TARGET_FLAGS}"

    # target specific copy of the common flags
    local flags=("${CMAKE_FLAGS[@]}")

    case ${TOOLCHAIN} in
        mingw)
            # cross compiler selection goes through a toolchain file,
            # CC/CXX/AR environment variables are not used here
            unset CC CXX
            local toolchain
            toolchain="$(pwd)/toolchain-mingw-w64.cmake"
            write_mingw_toolchain "${toolchain}"
            flags+=(-DCMAKE_TOOLCHAIN_FILE="${toolchain}")
            # LTO with mingw-w64 fails to link z3.exe (at least on some toolchains)
            flags+=(-DZ3_LINK_TIME_OPTIMIZATION=OFF)   # later -D wins
            ;;
        aarch64)
            # cross compiler selection goes through a toolchain file,
            # CC/CXX/AR environment variables are not used here
            unset CC CXX
            local toolchain
            toolchain="$(pwd)/toolchain-aarch64.cmake"
            write_aarch64_toolchain "${toolchain}"
            flags+=(-DCMAKE_TOOLCHAIN_FILE="${toolchain}")
            ;;
        *)
            export CC=gcc
            export CXX=g++
            ;;
    esac

    echo "Generating makefiles with cmake"
    cmake -G "Unix Makefiles" "../${WORKING_DIR}/" "${flags[@]}"

    echo "Compiling z3 ..."
    VERBOSE=1 cmake --build . --parallel "${NUMCPUS}"
    "${STRIP_CMD}" -s "${BIN}"

    check_binary

    cd "${ROOT}"
    echo "Build successful: ${ROOT}/${BUILD_DIR}/${BIN}"
    version_z3
}

# Copies the built executable of a target into its suitable subdirectory of
# the output directory.
deploy_z3()
{
    local target="$1"

    configure_target "${target}"
    local dest_dir="${OUT_DIR}/${DEST_SUBDIR}"

    echo "Copying ${BIN} to ${dest_dir} ..."

    if [ ! -d "${dest_dir}" ]; then
        mkdir -p "${dest_dir}"
    fi

    if [ -f "${dest_dir}/${BIN}" ]; then
        echo -n "Warning: ${BIN} already exists in ${dest_dir}. Overwrite? [Y/n] "
        read -r answer || answer=""
        if [ -n "${answer}" ]; then
            case ${answer} in
                y|Y|yes|Yes|YES)
                    ;;
                *)
                    echo "Aborting ..."
                    exit 1
                    ;;
            esac
        fi
    fi

    cp "${ROOT}/${BUILD_DIR}/${BIN}" "${dest_dir}/"
}

print_results()
{
    echo
    echo "Built z3 executables:"
    local target
    for target in "${SELECTED_TARGETS[@]}"; do
        configure_target "${target}"
        echo "  ${target}: ${OUT_DIR}/${DEST_SUBDIR}/${BIN}"
        if [ -f "${ROOT}/${BUILD_DIR_PREFIX}-${target}/VERSION.z3" ]; then
            echo "    z3 version: $(cat "${ROOT}/${BUILD_DIR_PREFIX}-${target}/VERSION.z3")"
        else
            echo "    Warning: z3 version information not available."
        fi
    done
}

cleanup()
{
    if [ ${DONTREMOVE} = true ]; then
        return
    fi

    # The built executables are deployed to the output directory, so the
    # build folders and the temporary Git checkout can be removed.
    local target
    for target in "${SELECTED_TARGETS[@]}"; do
        rm -rf "${BUILD_DIR_PREFIX}-${target}"
    done

    if [ ${DEFAULT_WORKING} = true ]; then
        rm -rf "${WORKING_DIR}"
    fi
}

add_target()
{
    local target t found dup
    for target in "$@"; do
        found=false
        for t in "${ALL_TARGETS[@]}"; do
            if [ "${target}" = "${t}" ]; then
                found=true
                break
            fi
        done
        if [ ${found} = false ]; then
            echo "Error: Unknown target: ${target}"
            echo
            print_help
            exit 1
        fi
        dup=false
        for t in "${SELECTED_TARGETS[@]}"; do
            if [ "${target}" = "${t}" ]; then
                dup=true
                break
            fi
        done
        if [ ${dup} = false ]; then
            SELECTED_TARGETS+=("${target}")
        fi
    done
}

# Handle arguments
while [[ $# -gt 0 ]]; do
    arg="$1"

    case $arg in
        -g|--git-dir)
            if [ -z "${2}" ]; then
                echo "Error: No git source directory specified"
                echo
                print_help
                exit 1
            fi
            WORKING_DIR="$2"
            DEFAULT_WORKING=false
            shift
            shift
            ;;
        -t|--targets)
            if [ -z "${2}" ]; then
                echo "Error: No target list specified"
                echo
                print_help
                exit 1
            fi
            IFS=',' read -r -a target_list <<< "${2}"
            add_target "${target_list[@]}"
            shift
            shift
            ;;
        -o|--output-dir)
            if [ -z "${2}" ]; then
                echo "Error: No output directory specified"
                echo
                print_help
                exit 1
            fi
            OUT_DIR="$2"
            DEFAULT_OUT=false
            shift
            shift
            ;;
        -v|--version)
            if [ -z "${2}" ]; then
                echo "Error: No version specified"
                echo
                print_help
                exit 1
            fi
            if [[ ! ${2} =~ ^[A-Za-z0-9._/-]+$ ]]; then
                echo "Error: Invalid version: ${2}"
                echo
                print_help
                exit 1
            fi
            Z3_VERSION_MODE="version"
            Z3_VERSION_REF="$2"
            shift
            shift
            ;;
        --latest)
            Z3_VERSION_MODE="latest"
            shift
            ;;
        --pinned)
            Z3_VERSION_MODE="pinned"
            shift
            ;;
        -j|--jobs)
            if [[ ! ${2} =~ ^[0-9]+$ ]]; then
                echo "Error: Invalid number of jobs: ${2}"
                echo
                print_help
                exit 1
            fi
            NUMCPUS="${2}"
            shift
            shift
            ;;
        -n|--no-pull)
            NOUPDATE=true
            shift
            ;;
        --no-remove-temp)
            DONTREMOVE=true
            shift
            ;;
        -h|--help)
            print_help
            exit 0
            ;;
        *)
            echo "Unrecognized argument: $arg"
            print_help
            exit 1
            ;;
    esac
done

if [ ${#SELECTED_TARGETS[@]} -eq 0 ]; then
    SELECTED_TARGETS=("${ALL_TARGETS[@]}")
fi

echo "Preparing environment..."
check_tools
print_setup
checkout_z3
update_z3

for target in "${SELECTED_TARGETS[@]}"; do
    compile_z3 "${target}"
    deploy_z3 "${target}"
done

print_results
cleanup

echo "All done."
