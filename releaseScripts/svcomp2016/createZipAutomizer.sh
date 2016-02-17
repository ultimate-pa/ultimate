#!/bin/bash
if [ $# -eq 0 ]; then
    echo "No arguments supplied -- use 'linux' or 'win32' as argument"
	exit 1
fi
if [ "$1" == "linux" ]; then
    echo "Building .zip for linux..."
	ARCH="linux"
	ARCHPATH="products/CLI-E4/linux/gtk/x86_64"
	Z3PATH="z3"
elif [ "$1" == "win32" ]; then
	echo "Building .zip for linux..."
	ARCH="win32"
	ARCHPATH="products/CLI-E4/win32/win32/x86_64"
	Z3PATH="z3.exe"
else
    echo "Wrong argument: ""$1"" -- use 'linux' or 'win32'"		
	exit 1
fi


TOOLNAME=Automizer
TARGETDIR=U${TOOLNAME}
TOOLCHAIN=../../trunk/examples/toolchains/AutomizerC_WitnessPrinter.xml
TERMTOOLCHAIN=../../trunk/examples/toolchains/BuchiAutomizerCWithBlockEncoding.xml
VALTOOLCHAIN=../../trunk/examples/toolchains/AutomizerC.xml
SETTINGS=../../trunk/examples/settings/svcomp2016/*${TOOLNAME}*

rm -r "$TARGETDIR"
rm Ultimate"$TOOLNAME".zip
mkdir "$TARGETDIR"
cp -a ../../trunk/source/BA_SiteRepository/target/${ARCHPATH}/* "$TARGETDIR"/
cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
cp "$TERMTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"Termination.xml
cp "$VALTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"WitnessValidation.xml
cp LICENSE* "$TARGETDIR"/
cp ${SETTINGS} "$TARGETDIR"/.
cp Ultimate.py "$TARGETDIR"/
cp Ultimate.ini "$TARGETDIR"/
cp README "$TARGETDIR"/
cp ${Z3PATH} "$TARGETDIR"/

# change Z3 memory settings for rcfgbuilder 
#for i in "$TARGETDIR"/*.epf; do awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\\ for\\ external\\ solver=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $i > $i.tmp && mv $i.tmp $i ; done

# change Z3 memory settings for buchiautomizer
#awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer/Command\\ for\\ external\\ solver\\ (rank\\ synthesis)=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $TERMSETTINGS > $TERMSETTINGS.tmp && mv $TERMSETTINGS.tmp $TERMSETTINGS

# set version 
VERSION=`git rev-parse HEAD | cut -c1-8`
echo $VERSION
sed "s/version =.*/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

zip -q Ultimate"$TOOLNAME"-"$ARCH"-"$VERSION".zip -r "$TARGETDIR"/*

