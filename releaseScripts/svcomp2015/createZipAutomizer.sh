#!/bin/bash

TOOLNAME=Automizer
TARGETDIR=Ultimate${TOOLNAME}
TOOLCHAIN=../../trunk/examples/toolchains/AutomizerC.xml
TERMTOOLCHAIN=../../trunk/examples/toolchains/BuchiAutomizerCWithBlockEncoding.xml
SETTINGS=../../trunk/examples/settings/svcomp2015/*${TOOLNAME}*
TERMSETTINGS="$TARGETDIR"/svComp-64bit-termination-Automizer.epf

rm -r "$TARGETDIR"
rm Ultimate"$TOOLNAME".zip
mkdir "$TARGETDIR"
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* "$TARGETDIR"/
cp "$TOOLCHAIN" "$TARGETDIR"/"$TOOLNAME".xml
cp "$TERMTOOLCHAIN" "$TARGETDIR"/"$TOOLNAME"Termination.xml
cp LICENSE* "$TARGETDIR"/
cp ${SETTINGS} "$TARGETDIR"/.
cp Ultimate.py "$TARGETDIR"/
cp Ultimate.ini "$TARGETDIR"/
cp README "$TARGETDIR"/

# change Z3 memory settings for rcfgbuilder 
for i in "$TARGETDIR"/*.epf; do awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\\ for\\ external\\ solver=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $i > $i.tmp && mv $i.tmp $i ; done

# change Z3 memory settings for buchiautomizer
awk '/@de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer=0.0.1/ { print; print "/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer/Command\\ for\\ external\\ solver\\ (rank\\ synthesis)=z3 SMTLIB2_COMPLIANT\\=true -memory\\:2500 -smt2 -in -t\\:12000"; next }1' $TERMSETTINGS > $TERMSETTINGS.tmp && mv $TERMSETTINGS.tmp $TERMSETTINGS

zip -q Ultimate"$TOOLNAME".zip -r "$TARGETDIR"/*

