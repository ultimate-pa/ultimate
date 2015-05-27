#!/bin/bash
mkdir BuchiAutomizer
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* BuchiAutomizer/
cp LICENSE* BuchiAutomizer/
cp ../../trunk/examples/toolchains/AutomizerAndBuchiAutomizerCWithBlockEncoding.xml BuchiAutomizer/
cp BuchiAutomizer.epf BuchiAutomizer/
cp buchiAutomizer.sh BuchiAutomizer/
cp Ultimate.ini BuchiAutomizer/
cp README BuchiAutomizer/
zip BuchiAutomizer.zip -r BuchiAutomizer/*

