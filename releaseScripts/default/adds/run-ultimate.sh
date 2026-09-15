#!/bin/bash 
# small script to wrap common Ultimate startup things 
java \
-Dosgi.configuration.area=config/ \
-Xmx10G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.8.0.v20260804-1928.jar \
-data config/data \
"$@"
