#!/bin/bash
# This script generates a directory that contains the DeltaDebugger 
# It takes additional binaries from the adds/ folder. Currently, we use z3, cvc4 and mathsat
# It also adds README, Ultimate.py, and various license files
# In contrast to createZip, it does not add toolchains or settings files and it does not generate a .zip, only the directory 

## Include the makeSettings shared functions 
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


if [ $# -le 0 ]; then
    echo $#
    echo "Not enough arguments supplied -- use arguments in the following order"
	echo "1. 'linux' or 'win32' for the target platform"
    exit 1
fi

TOOLNAME="DeltaDebugger"
LCTOOLNAME="$(echo $TOOLNAME | tr '[A-Z]' '[a-z]')"
echo "using $TOOLNAME ($LCTOOLNAME) as toolname"


if [ "$1" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/DeltaDebugger/linux/gtk/x86_64"
	Z3PATH="adds/z3"
	CVC4PATH="adds/cvc4"
	MATHSATPATH="adds/mathsat"
elif [ "$1" == "win32" ]; then
	echo "Building .zip for win32..."
	ARCH="win32"
	ARCHPATH="products/DeltaDebugger/win32/win32/x86_64"
	Z3PATH="adds/z3.exe"
	CVC4PATH="adds/cvc4.exe"
	MATHSATPATH="adds/mathsat.exe adds/mpir.dll adds/mathsat.dll"
else
    echo "Wrong argument: ""$1"" -- use 'linux' or 'win32'"		
	exit 1
fi


# set version 
VERSION=`git rev-parse HEAD | cut -c1-8`
echo "Version is "$VERSION
TARGETDIR=${TOOLNAME}-${ARCH}
CONFIGDIR="$TARGETDIR"/config
DATADIR="$TARGETDIR"/data

if [ -d "$TARGETDIR" ]; then
	echo "Removing old ""$TARGETDIR"
	rm -r "$TARGETDIR"
fi

echo "Copying files"
mkdir "$TARGETDIR"
mkdir "$CONFIGDIR"
mkdir "$DATADIR"

exit_on_fail cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
exit_on_fail cp adds/LICENSE* "$TARGETDIR"/
exit_on_fail cp adds/*LICENSE "$TARGETDIR"/
exit_on_fail cp adds/Ultimate.py "$TARGETDIR"/
exit_on_fail cp adds/Ultimate.ini "$TARGETDIR"/
exit_on_fail cp adds/README "$TARGETDIR"/
exit_on_fail cp ${Z3PATH} "$TARGETDIR"/
exit_on_fail cp ${CVC4PATH} "$TARGETDIR"/
exit_on_fail cp ${MATHSATPATH} "$TARGETDIR"/

echo "Modifying Ultimate.py with version and toolname"
## replacing version value in Ultimate.py
exit_on_fail sed "s/version =.*/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## replacing toolname value in Ultimate.py
exit_on_fail sed "s/toolname =.*/toolname = \'$TOOLNAME\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py


