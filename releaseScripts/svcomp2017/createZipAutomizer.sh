#!/bin/bash

# Build latest version of Z3 or copy binary from Monteverdi
# Get CVC4 here: http://cvc4.cs.nyu.edu/downloads/

function test {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
        echo "$@ failed with $1"
        exit $status
    fi
    return $status
}


if [ $# -eq 0 ]; then
    echo "No arguments supplied -- use 'linux' or 'win32' as argument"
	exit 1
fi
if [ "$1" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
	Z3PATH="adds/z3"
	CVC4PATH="adds/cvc4"
elif [ "$1" == "win32" ]; then
	echo "Building .zip for win32..."
	ARCH="win32"
	ARCHPATH="products/CLI-E4/win32/win32/x86_64"
	Z3PATH="adds/z3.exe"
	CVC4PATH="adds/cvc4.exe"
else
    echo "Wrong argument: ""$1"" -- use 'linux' or 'win32'"		
	exit 1
fi

# set version 
VERSION=`git rev-parse HEAD | cut -c1-8`
echo "Version is "$VERSION
TOOLNAME=Automizer
TARGETDIR=U${TOOLNAME}-${ARCH}
ZIPFILE=Ultimate${TOOLNAME}-${ARCH}.zip
TOOLCHAIN=../../trunk/examples/toolchains/AutomizerC_WitnessPrinter.xml
TERMTOOLCHAIN=../../trunk/examples/toolchains/BuchiAutomizerCWithBlockEncoding.xml
VALTOOLCHAIN=../../trunk/examples/toolchains/AutomizerC.xml
SETTINGS=../../trunk/examples/settings/svcomp2017/automizer/*${TOOLNAME}*

if [ -d "$TARGETDIR" ]; then
	echo "Removing old ""$TARGETDIR"
	rm -r "$TARGETDIR"
fi
if [ -f "${ZIPFILE}" ]; then
    echo "Removing old .zip file ""${ZIPFILE}"
	rm "${ZIPFILE}"
fi

echo "Copying files"
mkdir "$TARGETDIR"
test cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
test cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
test cp "$TERMTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"Termination.xml
test cp "$VALTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"WitnessValidation.xml
test cp adds/LICENSE* "$TARGETDIR"/
test cp ${SETTINGS} "$TARGETDIR"/.
test cp adds/Ultimate.py "$TARGETDIR"/
test cp adds/Ultimate.ini "$TARGETDIR"/
test cp adds/README "$TARGETDIR"/
test cp ${Z3PATH} "$TARGETDIR"/
test cp ${CVC4PATH} "$TARGETDIR"/

# change Z3 memory settings for rcfgbuilder 
#for i in "$TARGETDIR"/*.epf; do awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\\ for\\ external\\ solver=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $i > $i.tmp && mv $i.tmp $i ; done

# change Z3 memory settings for buchiautomizer
#awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer/Command\\ for\\ external\\ solver\\ (rank\\ synthesis)=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $TERMSETTINGS > $TERMSETTINGS.tmp && mv $TERMSETTINGS.tmp $TERMSETTINGS

echo "Creating .zip"
## replacing version value in Ultimate.py
test sed "s/version =.*/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

## creating new zipfile 
test zip -q ${ZIPFILE} -r "$TARGETDIR"/*

