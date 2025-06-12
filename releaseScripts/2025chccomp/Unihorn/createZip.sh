#!/bin/bash
mkdir StarExecArchive
mkdir StarExecArchive/Ultimate
cp -a ../../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* StarExecArchive/Ultimate/
cp LICENSE* StarExecArchive/Ultimate/
cp starexec_description.txt StarExecArchive/
cp ../../../trunk/examples/toolchains/AutomizerCHC.xml StarExecArchive/
cp chc-comp-wrapper.sh StarExecArchive/
cp Ultimate.ini StarExecArchive/Ultimate/
cp ../../../trunk/examples/settings/default/unihorn/chccomp-Unihorn_Default.epf StarExecArchive/
cp -LR ../../default/adds/z3 StarExecArchive/Ultimate/
cp -LR ../../default/adds/z3-LICENSE StarExecArchive/Ultimate/

cd StarExecArchive
zip ../UltimateCommandline.zip -r *

