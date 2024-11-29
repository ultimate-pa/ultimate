#!/bin/bash 
# small script to wrap common Ultimate startup things 
java \
-Dosgi.configuration.area=config/ \
-Xmx10G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.6.800.v20240513-1750.jar \
-data config/data \
"$@"
