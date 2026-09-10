#!/bin/bash 
# small script to wrap common Ultimate startup things 
java \
-Dosgi.configuration.area=config/ \
-Xmx10G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.7.100.v20251111-0406.jar \
-data config/data \
"$@"
