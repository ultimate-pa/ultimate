#!/bin/bash
mkdir AutomizerConcurrent
cp -a ../../trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/* AutomizerConcurrent/
cp LICENSE* AutomizerConcurrent/
cp ../../trunk/examples/toolchains/TraceAbstractionConcurrent.xml AutomizerConcurrent/
cp AutomizerConcurrentDefaultSettings.epf AutomizerConcurrent/
cp AutomizerConcurrent.sh AutomizerConcurrent/
cp Ultimate.ini AutomizerConcurrent/
cp README AutomizerConcurrent/
mkdir AutomizerConcurrent/examples/
cp ../../trunk/examples/concurrent/regression/*.bpl AutomizerConcurrent/examples/
zip AutomizerConcurrent.zip -r AutomizerConcurrent/*
