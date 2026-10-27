#!/bin/bash
#
# Creates a statically linked version of z3 from the repository using generic
# CFLAGS in order to allow for maximum compatibility with different
# architectures.
#
# The output binary of z3 will be put in the directory DEST_DIR, default is z3.
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
COMMON_FLAGS="-O2 -march=x86-64 -mtune=generic -pipe"

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

WORKING_DIR="z3temp"
DEFAULT_WORKING=true
BUILD_DIR="buildtemp"
DEST_DIR="z3"
DEFAULT_DEST=true
NUMCPUS=$(grep -c '^processor' /proc/cpuinfo)
NUMCPUS=$((NUMCPUS + 1))
NOUPDATE=false
DONTREMOVE=false
WINDOWS=false

# Target specific settings, set by configure_target()
BIN=""
STRIP_CMD=""

ROOT="$(pwd)"
trap 'cd "${ROOT}"' EXIT

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
    echo "  -d|--dest-dir dest-dir      Specifies the destination directory"
    echo "                              in which the z3 binary will be placed."
    echo "                              Default: ${DEST_DIR}"
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
    echo "  --windows                   Cross-compile with mingw-w64 for Windows."
    echo "                              For debian system, you need to"
    echo "                              - apt-get install mingw-w64"
    echo "                              - update-alternatives --config ${MINGW_PREFIX}-g++"
    echo "                                and select POSIX compliant threading"
    echo "                                (same for ${MINGW_PREFIX}-gcc)"
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
    echo -en "  dest-dir:\t\t\t${DEST_DIR}"
    if [ ${DEFAULT_DEST} = true ]; then
        echo " (default)"
    else
        echo
    fi
    echo -e "  Target:\t\t\t$([ ${WINDOWS} = true ] && echo "Windows (mingw-w64)" || echo "Linux")"
    echo -e "  Additional parameters:\t${CMAKE_FLAGS[*]}"
    echo -e "  CFLAGS and CXXFLAGS:\t\t${COMMON_FLAGS}"
    echo -e "  Number of parallel jobs:\t${NUMCPUS}"
    echo
}

configure_target()
{
    if [ ${WINDOWS} = true ]; then
        BIN="z3.exe"
        STRIP_CMD="${MINGW_PREFIX}-strip"
        for tool in gcc g++ strip; do
            if ! command -v "${MINGW_PREFIX}-${tool}" &> /dev/null ; then
                echo "Error: ${MINGW_PREFIX}-${tool} not found. Is mingw-w64 installed?"
                exit 1
            fi
        done
    else
        BIN="z3"
        STRIP_CMD="strip"
    fi
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

    git pull
    cd "${ROOT}"
}

version_z3()
{
    cd "${WORKING_DIR}"
    TAG=$(git describe --tags "$(git rev-list --tags --max-count=1)")
    VERSION_HASH=$(git rev-parse --short HEAD)
    BRANCH=$(git branch | grep \* | cut -d ' ' -f2-)
    cd "${BUILD_DIR}"

    Z3_VERSION="${TAG}-${BRANCH}-${VERSION_HASH}"
    echo "z3 version is: ${Z3_VERSION}"
    echo "${Z3_VERSION}" > "VERSION.z3"
    cd "${ROOT}"
}

check_binary()
{
    if [ ${WINDOWS} = true ]; then
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
    echo "Building z3 ..."
    cd "${WORKING_DIR}"
    if [ -d "${BUILD_DIR}" ]; then
        rm -rf "${BUILD_DIR}"
    fi
    mkdir "${BUILD_DIR}"
    cd "${BUILD_DIR}"

    export CFLAGS="${COMMON_FLAGS}"
    export CXXFLAGS="${COMMON_FLAGS}"

    # target specific copy of the common flags
    local flags=("${CMAKE_FLAGS[@]}")

    if [ ${WINDOWS} = true ] ; then
        # cross compiler selection goes through a toolchain file,
        # CC/CXX/AR environment variables are not used here
        local toolchain
        toolchain="$(pwd)/toolchain-mingw-w64.cmake"
        write_mingw_toolchain "${toolchain}"
        flags+=(-DCMAKE_TOOLCHAIN_FILE="${toolchain}")
        # LTO with mingw-w64 fails to link z3.exe (at least on some toolchains)
        flags+=(-DZ3_LINK_TIME_OPTIMIZATION=OFF)   # later -D wins
    else
        export CC=gcc
        export CXX=g++
    fi

    echo "Generating makefiles with cmake"
    cmake -G "Unix Makefiles" ../ "${flags[@]}"

    echo "Compiling z3 ..."
    VERBOSE=1 cmake --build . --parallel "${NUMCPUS}"
    "${STRIP_CMD}" -s "${BIN}"

    check_binary

    cd "${ROOT}"
    echo "Build successful."
    version_z3
}

deploy_z3()
{
    echo "Copying created executable to ${DEST_DIR} ..."

    if [ -d "${DEST_DIR}" ]; then
        if [ -f "${DEST_DIR}/${BIN}" ]; then
            echo -n "Warning: ${BIN} already exists in ${DEST_DIR}. Overwrite? [Y/n] "
            read -r answer
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
    else
        mkdir "${DEST_DIR}"
    fi

    cp "${WORKING_DIR}/${BUILD_DIR}/${BIN}" "${DEST_DIR}/"

    if [ ! -f "${WORKING_DIR}/${BUILD_DIR}/VERSION.z3" ]; then
        echo "Warning: z3 version information not available."
        echo "         Remove the directory ${WORKING_DIR}/${BUILD_DIR}"
        echo "         and run this script again if version information is required."
    fi
    cp "${WORKING_DIR}/${BUILD_DIR}/VERSION.z3" "${DEST_DIR}/"
}

cleanup()
{
    if [ ${DONTREMOVE} = true ]; then
        return
    fi

    cd "${WORKING_DIR}"

    rm -r "${BUILD_DIR}"

    cd "${ROOT}"

    if [ ${DEFAULT_WORKING} = true ]; then
        rm -rf "${WORKING_DIR}/.git"
        rm -r "${WORKING_DIR}"
    fi
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
        -d|--dest-dir)
            if [ -z "${2}" ]; then
                echo "Error: No destination directory specified"
                echo
                print_help
                exit 1
            fi
            DEST_DIR="$2"
            DEFAULT_DEST=false
            shift
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
        --windows)
            WINDOWS=true
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

echo "Preparing environment..."
configure_target
print_setup
checkout_z3
update_z3
compile_z3
deploy_z3
cleanup

echo "All done."
