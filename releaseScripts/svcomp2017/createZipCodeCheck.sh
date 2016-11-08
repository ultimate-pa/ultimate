#!/bin/bash

TOOLNAME=Kojak
TARGETDIR=U${TOOLNAME}
TOOLCHAIN=../../trunk/examples/toolchains/KojakC.xml
SETTINGS=../../trunk/examples/settings/svcomp2017/kojak/*Kojak*

rm -r "$TARGETDIR"
rm Ultimate"$TOOLNAME".zip
mkdir "$TARGETDIR"
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* "$TARGETDIR"/
cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
cp adds/LICENSE* "$TARGETDIR"/
cp ${SETTINGS} "$TARGETDIR"/.
cp adds/Ultimate.py "$TARGETDIR"/
cp adds/Ultimate.ini "$TARGETDIR"/
cp adds/README "$TARGETDIR"/
cp adds/z3 "$TARGETDIR"/

# change Z3 memory settings
#for i in "$TARGETDIR"/*.epf; do awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\\ for\\ external\\ solver=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $i > $i.tmp && mv $i.tmp $i ; done

# set version
VERSION=`git rev-parse HEAD | cut -c1-8`
echo $VERSION
sed "s/version =.*/version = \'$VERSION\'/g" "$TARGETDIR"/Ultimate.py > "$TARGETDIR"/Ultimate.py.tmp && mv "$TARGETDIR"/Ultimate.py.tmp "$TARGETDIR"/Ultimate.py && chmod a+x "$TARGETDIR"/Ultimate.py

zip -q Ultimate"$TOOLNAME".zip -r "$TARGETDIR"/*

