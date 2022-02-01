#!/bin/bash
mkdir kojak
cp -a ../../source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/* kojak/
cp ../LICENSE* kojak/
cp ./ToolchainKojakC.xml kojak/
cp ../../examples/settings/AlexSVCOMPstandard kojak/
cp ../../examples/settings/AlexSVCOMPmemsafety kojak/
cp ./Ultimate.ini kojak/
cp KojakSvComp.py kojak/
zip UltimateKojakCommandline.zip -r kojak/*
