#!/bin/bash
mkdir StarExecArchive
mkdir StarExecArchive/bin
mkdir StarExecArchive/Ultimate
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/* StarExecArchive/Ultimate/
cp LICENSE* StarExecArchive/Ultimate/
cp starexec_description.txt StarExecArchive/
cp ../../trunk/examples/toolchains/AutomizerAndBuchiAutomizerCWithBlockEncoding.xml StarExecArchive/
cp starexec_run_default StarExecArchive/bin
cp Ultimate.ini StarExecArchive/Ultimate/
cp settings.epf StarExecArchive/
cp -R /opt/z3-4.3.2.d548c51a984e-x64-debian-6.0.6 StarExecArchive/
cd StarExecArchive
zip ../UltimateCommandline.zip -r *

