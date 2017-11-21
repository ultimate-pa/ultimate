#!/bin/bash

function exitOnFail {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		echo "$@ failed with $1"
		exit $status
    fi
    return $status
}

pushd ../../trunk/source/BA_MavenParentUltimate/ > /dev/null
exitOnFail mvn clean install -Pmaterialize
popd > /dev/null

# createZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
# Taipan 
exitOnFail bash createZip.sh Taipan linux AutomizerCInline_WitnessPrinter.xml NONE AutomizerCInline.xml AutomizerCInline_WitnessPrinter.xml NONE NONE

# Automizer without separate blockencoding plugin 
#exitOnFail bash createZip.sh Automizer linux AutomizerC_WitnessPrinter.xml BuchiAutomizerCInline_WitnessPrinter.xml AutomizerC.xml AutomizerC_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

# Automizer with separate blockencoding plugin 
exitOnFail bash createZip.sh Automizer linux AutomizerC_BE_WitnessPrinter.xml BuchiAutomizerCInline_BE_WitnessPrinter.xml AutomizerC.xml AutomizerC_BE_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

# Kojak 
exitOnFail bash createZip.sh Kojak linux KojakC_WitnessPrinter.xml NONE NONE KojakC_WitnessPrinter.xml NONE NONE

# DeltaDebugger
exitOnFail bash createDeltaDebuggerDir.sh linux 

exit 0
