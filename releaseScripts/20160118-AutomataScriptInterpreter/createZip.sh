#!/bin/bash
mkdir Ultimate
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* Ultimate/
cp LICENSE* Ultimate
cp ../../trunk/examples/toolchains/AutomataScriptInterpreter.xml Ultimate/
cp AutomataScriptInterpreter.sh Ultimate/
cp Ultimate.ini Ultimate/
cp README Ultimate/
zip UltimateAutomataScriptInterpreter.zip -r Ultimate/*
