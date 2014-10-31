#!/bin/bash

TOOLNAME=CodeCheck
TARGETDIR=Ultimate${TOOLNAME}
TOOLCHAIN=../../trunk/examples/toolchains/CodeCheckWithBE-C.xml
SETTINGS=../../trunk/examples/settings/svcomp2015/*Kojak*

mkdir "$TARGETDIR"
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* "$TARGETDIR"/
cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
cp LICENSE* "$TARGETDIR"/
cp ${SETTINGS} "$TARGETDIR"/.
cp Ultimate.py "$TARGETDIR"/
cp Ultimate.ini "$TARGETDIR"/
cp README "$TARGETDIR"/
zip Ultimate"$TOOLNAME".zip -r "$TARGETDIR"/*

