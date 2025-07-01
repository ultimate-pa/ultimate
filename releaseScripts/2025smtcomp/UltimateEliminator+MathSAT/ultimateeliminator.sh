#!/bin/bash
# Run script for Ultimate Eliminator
SCRIPTDIR=`dirname $0`
java -Dosgi.configuration.area=$SCRIPTDIR/config/ -Xmx40G -Xss4m -jar $SCRIPTDIR/plugins/org.eclipse.equinox.launcher_1.6.800.v20240513-1750.jar -s $SCRIPTDIR/mathsat.epf -external-solver "$SCRIPTDIR/mathsat" "$@"

