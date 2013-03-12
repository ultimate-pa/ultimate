#!/bin/bash

trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs \
"TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
"TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-svcomp-StrongestMinimize" \
"TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-svcomp-LargeStrongest"

# trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs/minitests \
# "TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-EagerPost-Hoare" \


# trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp13/trunk/ntdrivers-simplified/ \
# "TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-svcomp-EagerMinimize" \
# "TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-svcomp-LazyMinimize" \
# "TraceAbstraction.xml;TraceAbstractionC.xml;TraceAbstraction-svcomp-StrongestMinimize"
