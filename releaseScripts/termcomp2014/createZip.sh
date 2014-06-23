#!/bin/bash
mkdir automizer
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/* automizer/
cp ../LICENSE* automizer/
cp starexec_description.txt automizer/
cp ../../trunk/examples/toolchains/BuchiAutomizerCWithBlockEncoding.xml automizer/
cp BuchiAutomizer.sh automizer/
cp Ultimate.ini automizer/
cp settings.epf automizer/
zip UltimateCommandline.zip -r automizer/*
