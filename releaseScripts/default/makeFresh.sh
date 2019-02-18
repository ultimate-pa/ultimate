#!/bin/bash
# This script builds Ultimate with maven and then calls makeZip.sh for all tools that can be deployed. 

## include the makeSettings shared functions 
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"


## start the actual script 
pushd ../../trunk/source/BA_MavenParentUltimate/ > /dev/null
test mvn -T 1C clean install -Pmaterialize
popd > /dev/null

for platform in {linux,win32}; do
    # createZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
    # Taipan 
    exitOnFail bash createZip.sh Taipan $platform AutomizerCInline_WitnessPrinter.xml NONE AutomizerCInline.xml AutomizerCInline_WitnessPrinter.xml NONE NONE

    # Automizer without separate blockencoding plugin 
    exitOnFail bash createZip.sh Automizer $platform AutomizerCInline_WitnessPrinter.xml BuchiAutomizerCInline_WitnessPrinter.xml AutomizerC.xml AutomizerC_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

    # Automizer with separate blockencoding plugin 
    #exitOnFail bash createZip.sh Automizer linux AutomizerC_BE_WitnessPrinter.xml BuchiAutomizerCInline_BE_WitnessPrinter.xml AutomizerC.xml AutomizerC_BE_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

    # Kojak 
    exitOnFail bash createZip.sh Kojak $platform KojakC_WitnessPrinter.xml NONE NONE KojakC_WitnessPrinter.xml NONE NONE

    # DeltaDebugger
    exitOnFail bash createDeltaDebuggerDir.sh $platform 
done 

exit 0
