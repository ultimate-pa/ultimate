#!/bin/bash
mkdir UltimateEliminator
# mkdir UltimateEliminator/bin
# mkdir UltimateEliminator/Ultimate
cp -a ../../../trunk/source/BA_SiteRepository/target/products/UltimateEliminator/linux/gtk/x86_64/* UltimateEliminator/
rm UltimateEliminator/Ultimate.ini
#cp *LICENSE* UltimateEliminator/cp smtlib2_trace_executor StarExecArchive/bin/
cp ../../../trunk/examples/settings/UltimateEliminator/mathsat.epf UltimateEliminator/
cp ultimateeliminator.sh UltimateEliminator/

cp -LR mathsat UltimateEliminator

# cp -a java/jdk-11.0.2 UltimateEliminator/


cd UltimateEliminator
zip ../UltimateEliminator.zip -r *

