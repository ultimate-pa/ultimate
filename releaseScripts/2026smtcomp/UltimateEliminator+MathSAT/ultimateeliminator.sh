#!/bin/bash
# Run script for Ultimate Eliminator
SCRIPTDIR=`dirname $0`
java -Dosgi.configuration.area=$SCRIPTDIR/config/ -Xmx40G -Xss4m -jar $SCRIPTDIR/plugins/org.eclipse.equinox.launcher_1.7.0.v20250519-0528.jar -s $SCRIPTDIR/mathsat.epf -external-solver "$SCRIPTDIR/mathsat" "$@"

