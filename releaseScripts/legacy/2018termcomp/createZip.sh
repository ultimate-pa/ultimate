#!/bin/bash
mkdir StarExecArchive
mkdir StarExecArchive/bin
mkdir StarExecArchive/Ultimate
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* StarExecArchive/Ultimate/
cp LICENSE* StarExecArchive/Ultimate/
cp starexec_description.txt StarExecArchive/
cp ../../trunk/examples/toolchains/AutomizerAndBuchiAutomizerCInlineWithBlockEncoding.xml StarExecArchive/
cp starexec_run_* StarExecArchive/bin/
cp Ultimate.ini StarExecArchive/Ultimate/
cp ../../trunk/examples/settings/buchiAutomizer/termcomp2017.epf StarExecArchive/
cp ../../trunk/examples/settings/buchiAutomizer/termcomp2017-NontrivialArrayWrites.epf StarExecArchive/
#mkdir StarExecArchive/z3
cp -LR ./z3 StarExecArchive/bin/
cp starexec_run_z3test StarExecArchive/bin/

cd StarExecArchive
zip ../UltimateCommandline.zip -r *

