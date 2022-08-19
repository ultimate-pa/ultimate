#!/bin/bash

TOOLNAME=Kojak
TARGETDIR=Ultimate${TOOLNAME}
TOOLCHAIN=../../trunk/examples/toolchains/CodeCheckWithBE-C.xml
SETTINGS=../../trunk/examples/settings/svcomp2015/*Impulse*

rm -r "$TARGETDIR"
rm Ultimate"$TOOLNAME".zip
mkdir "$TARGETDIR"
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* "$TARGETDIR"/
cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
cp LICENSE* "$TARGETDIR"/
cp ${SETTINGS} "$TARGETDIR"/.
cp Ultimate.py "$TARGETDIR"/
cp Ultimate.ini "$TARGETDIR"/
cp README "$TARGETDIR"/

# change Z3 memory settings
for i in "$TARGETDIR"/*.epf; do awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\\ for\\ external\\ solver=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $i > $i.tmp && mv $i.tmp $i ; done

zip -q Ultimate"$TOOLNAME".zip -r "$TARGETDIR"/*

