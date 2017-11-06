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

set -e

GIT_FETCH_URL="https://github.com/Z3Prover/z3.git"
ADDITIONAL_FLAGS="--staticbin"

WORKING_DIR="z3temp"
DEFAULT_WORKING=true
BUILD_DIR="buildtemp"
DEST_DIR="z3"
DEFAULT_DEST=true
NUMCPUS=`grep -c '^processor' /proc/cpuinfo`
NUMCPUS=$((${NUMCPUS} + 1))
NOUPDATE=false
DONTREMOVE=false

ROOT="`pwd`"
trap 'cd "${ROOT}"' EXIT

function print_help()
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
	echo "  -h | --help                 Print this help."
}

function print_setup()
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
	else echo
	fi
	echo -e "  Additional parameters:\t${ADDITIONAL_FLAGS}"
	echo -e "  Number of parallel jobs:\t${NUMCPUS}"
}

function checkout_z3()
{
	if [ ${DEFAULT_WORKING} = false ]; then
		return
	fi

	echo "Cloning z3 into ${WORKING_DIR} ..."

	mkdir "${WORKING_DIR}"
	cd "${WORKING_DIR}"
	git clone "${GIT_FETCH_URL}" .
	cd "${ROOT}"
}

function update_z3()
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

function version_z3()
{
	cd "${WORKING_DIR}"
	TAG=$(git describe --tags $(git rev-list --tags --max-count=1))
	VERSION_HASH=$(git rev-parse --short HEAD)
	BRANCH=$(git branch | grep \* | cut -d ' ' -f2-)
	cd "${BUILD_DIR}"

	Z3_VERSION="${TAG}-${BRANCH}-${VERSION_HASH}"
	echo "z3 version is: ${Z3_VERSION}"
	echo "${Z3_VERSION}" > "VERSION.z3"
	cd "${ROOT}"
}

function compile_z3()
{
	echo "Building z3 ..."
	cd "${WORKING_DIR}"

	if [ -d "${BUILD_DIR}" ]; then
		EXISTING=$(dirname $(readlink -e "${BUILD_DIR}"))
		echo -n "Warning: Build directory ${EXISTING} already exists. Remove? [Y/n] "
		read answer
		if [ ! -z ${answer} ]; then
			case ${answer} in
				y|Y|yes|Yes|YES)
					;;
				*)
					if [ -f "${BUILD_DIR}/z3" ]; then
						echo -n "Use previously built z3 version? [y/N] "
						read answerp
						if [ ! -z ${answerp} ]; then
							case ${answerp} in
								y|Y|yes|Yes|YES)
									cd "${ROOT}"
									return
									;;
								*)
									;;
							esac
						fi
					fi
					echo "Aborting..."
					cd "${ROOT}"
					exit 1
					;;
			esac
		fi
		rm -rf "${BUILD_DIR}"
	fi

	CXXFLAGS="-march=x86-64 -mtune=generic" python2 scripts/mk_make.py --build="${BUILD_DIR}" ${ADDITIONAL_FLAGS}

	cd "${BUILD_DIR}"
	echo "Compiling z3 ..."
	make ${MAKEOPTS}
	strip -s z3
	cd "${ROOT}"

	echo "Build successful."

	version_z3
}

function deploy_z3()
{
	echo "Copying created executable to ${DEST_DIR} ..."

	if [ -d "${DEST_DIR}" ]; then
		if [ -f "${DEST_DIR}/z3" ]; then
			echo -n "Warning: z3 already exists in ${DEST_DIR}. Overwrite? [Y/n] "
			read answer
			if [ ! -z ${answer} ]; then
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

	cp "${WORKING_DIR}/${BUILD_DIR}/z3" "${DEST_DIR}/"

	if [ ! -f "${WORKING_DIR}/${BUILD_DIR}/VERSION.z3" ]; then
		echo "Warning: z3 version information not available."
		echo "         Remove the directory ${WORKING_DIR}/${BUILD_DIR}"
		echo "         and run this script again if version information is required."
	fi
	cp "${WORKING_DIR}/${BUILD_DIR}/VERSION.z3" "${DEST_DIR}/"
}

function cleanup()
{
	if [ ${DONTREMOVE} = true ]; then
		return
	fi

	cd "${WORKING_DIR}"

	rm -rv "${BUILD_DIR}"

	cd "${ROOT}"

	if [ ${DEFAULT_WORKING} = true ]; then
		rm -rf "${WORKING_DIR}/.git"
		rm -rv "${WORKING_DIR}"
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
MAKEOPTS="-j${NUMCPUS}"
print_setup
checkout_z3
update_z3
compile_z3
deploy_z3
cleanup

echo "All done."
