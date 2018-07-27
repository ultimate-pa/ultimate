#!/bin/bash 
# small script to wrap common Ultimate startup things 
java \
-Dosgi.configuration.area=config/ \
-Xmx10G \
-Xss4m \
-jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar \
-data config/data \
"$@"
