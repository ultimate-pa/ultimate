#!/bin/bash
mkdir StarExecArchive
mkdir StarExecArchive/bin
mkdir StarExecArchive/Ultimate
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* StarExecArchive/Ultimate/
cp *LICENSE* StarExecArchive/Ultimate/
cp starexec_description.txt StarExecArchive/
cp ../../trunk/examples/toolchains/Empty.xml StarExecArchive/
cp starexec_run_* StarExecArchive/bin/
cp Ultimate.ini StarExecArchive/Ultimate/
cp ../../trunk/examples/settings/UltimateEliminator/* StarExecArchive/
# cp -LR /opt/bin/yices-smt2 StarExecArchive/bin/
cp -LR /opt/bin/mathsat StarExecArchive/bin/


cd StarExecArchive
zip ../UltimateCommandline.zip -r *

