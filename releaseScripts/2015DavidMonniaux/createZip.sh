#!/bin/bash
mkdir buchiAutomizer
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* buchiAutomizer/
cp LICENSE* buchiAutomizer/
cp ../../trunk/examples/toolchains/BuchiAutomizerCWithBlockEncoding.xml buchiAutomizer/
cp BuchiAutomizerDefaultSettings.epf buchiAutomizer/
cp buchiAutomizer.sh buchiAutomizer/
cp Ultimate.ini buchiAutomizer/
cp README buchiAutomizer/
zip UltimateCommandline.zip -r buchiAutomizer/*
