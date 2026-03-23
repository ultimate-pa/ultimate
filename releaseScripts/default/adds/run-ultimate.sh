#!/bin/bash 
# small script to wrap common Ultimate startup things 
java \
-Dosgi.configuration.area=config/ \
-Xmx10G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.7.0.v20250519-0528.jar \
-data config/data \
"$@"
