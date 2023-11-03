#!/bin/bash
mkdir StarExecArchive
mkdir StarExecArchive/bin
mkdir StarExecArchive/Ultimate
cp -a ../../../trunk/source/BA_SiteRepository/target/products/UltimateEliminator/linux/gtk/x86_64/* StarExecArchive/Ultimate/
rm StarExecArchive/Ultimate/Ultimate
rm StarExecArchive/Ultimate/Ultimate.ini
cp *LICENSE* StarExecArchive/Ultimate/
cp starexec_description.txt StarExecArchive/
cp starexec_run_* StarExecArchive/bin/
cp ../../../trunk/examples/settings/UltimateEliminator/* StarExecArchive/
cp -LR ../adds/yices-smt2 StarExecArchive/Ultimate/



cd StarExecArchive
zip ../UltimateCommandline.zip -r *

