#!/bin/bash
# This script generates a zip file for each Ultimate tool that should be deployed to GitHub or to some place else
# It takes additional binaries from the adds/ folder. Currently, we use z3, cvc4 and mathsat
# It also adds README, Ultimate.py, and various license files

function test {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        echo "$@ failed with $1"
        exit $status
    fi
    return $status
}

function copy_if_non_empty {
    local source="$1"
    local target="$2"
    if [ ! -z "$source" ]; then
        test cp "$source" "$target"
    fi
}

if [ $# -lt 4 ]; then
    echo "Not enough arguments supplied -- use arguments in the following order"
	echo "1. the toolname"
	echo "2. 'linux' or 'win32' for the target platform"
	echo "3. ReqCheck toolchain (e.g., 'ReqCheck.xml')"
	echo "4. TestGen toolchain (e.g., 'ReqToTest.xml')"
    exit 1
fi

TOOLNAME="$1"
if [ -z "$TOOLNAME" ]; then
	echo "First argument (toolname) cannot be empty"
	exit 1
fi
LCTOOLNAME="$(echo $TOOLNAME | tr '[A-Z]' '[a-z]')"
echo "Using $TOOLNAME ($LCTOOLNAME) as toolname"


# additional files for all architectures
ADDS=(
    "adds/LICENSE*"
    "adds/*LICENSE"
    "adds/reqchecker/README"
    "adds/reqchecker/run_complete_analysis.py"
)

# architecture-specific variables
if [ "$2" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
    ADDS+=("adds/z3" "adds/cvc4nyu" "adds/cvc4" "adds/mathsat")
elif [ "$2" == "win32" ]; then
	echo "Building .zip for win32..."
	ARCH="win32"
	ARCHPATH="products/CLI-E4/win32/win32/x86_64"
    ADDS+=("adds/z3.exe" "adds/cvc4nyu.exe" "adds/cvc4.exe" "adds/mathsat.exe" "adds/mpir.dll" "adds/mathsat.dll")
else
    echo "Wrong argument: ""$2"" -- use 'linux' or 'win32'"
	exit 1
fi


# set version
VERSION=`git rev-parse HEAD | cut -c1-8`
echo "Version is "$VERSION


TARGETDIR=U${TOOLNAME}-${ARCH}
CONFIGDIR="$TARGETDIR"/config
DATADIR="$TARGETDIR"/data
ZIPFILE=U${TOOLNAME}-${ARCH}.zip
SETTINGS=../../trunk/examples/settings/default/${LCTOOLNAME}/*${TOOLNAME}*

# check toolchain argument
if [ ! -z "$3" -a ! "NONE" = "$3" ]; then
	TOOLCHAIN=../../trunk/examples/toolchains/${3}
else
	echo "No reach toolchain specified, ommitting..."
	TOOLCHAIN=
fi

if [ ! -z "$4" -a ! "NONE" = "$4" ]; then
	TESTTOOLCHAIN=../../trunk/examples/toolchains/${4}
else
	echo "No test toolchain specified, ommitting..."
	TESTTOOLCHAIN=
fi

## removing files and dirs from previous deployments
if [ -d "$TARGETDIR" ]; then
	echo "Removing old $TARGETDIR"
	rm -r "$TARGETDIR"
fi

if [ -f "${ZIPFILE}" ]; then
    echo "Removing old .zip file ${ZIPFILE}"
	rm "${ZIPFILE}"
fi

## start copying files
echo "Copying files"
mkdir "$TARGETDIR"
mkdir "$CONFIGDIR"
mkdir "$DATADIR"

test cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
copy_if_non_empty "$TOOLCHAIN" "$CONFIGDIR"/ReqCheck.xml
copy_if_non_empty "$TESTTOOLCHAIN" "$CONFIGDIR"/ReqToTest.xml
test cp ${SETTINGS} "$CONFIGDIR"/.

## copy all adds to target dir
for add in "${ADDS[@]}" ; do
    if ! readlink -fe $add > /dev/null ; then
        echo "$add does not exist, aborting..."
        exit 1
    fi
    test cp $add "$TARGETDIR"/
done

## creating new zipfile
echo "Creating .zip"
test zip -q ${ZIPFILE} -r "$TARGETDIR"/*
