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
exitOnFail mvn -T 1C clean install -Pmaterialize
popd > /dev/null

for platform in {linux,win32}; do
    # createZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
    # Taipan 
    exitOnFail bash createZip.sh Taipan $platform AutomizerCInline_WitnessPrinter.xml NONE AutomizerCInline.xml AutomizerCInline_WitnessPrinter.xml NONE NONE

    # Automizer without separate blockencoding plugin 
    exitOnFail bash createZip.sh Automizer $platform AutomizerC_WitnessPrinter.xml BuchiAutomizerCInline_WitnessPrinter.xml AutomizerC.xml AutomizerC_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

    # Automizer with separate blockencoding plugin 
    #exitOnFail bash createZip.sh Automizer linux AutomizerC_BE_WitnessPrinter.xml BuchiAutomizerCInline_BE_WitnessPrinter.xml AutomizerC.xml AutomizerC_BE_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

    # Kojak 
    exitOnFail bash createZip.sh Kojak $platform KojakC_WitnessPrinter.xml NONE NONE KojakC_WitnessPrinter.xml NONE NONE

    # DeltaDebugger
    exitOnFail bash createDeltaDebuggerDir.sh $platform 
done 

exit 0
