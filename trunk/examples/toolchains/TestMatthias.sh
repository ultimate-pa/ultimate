#!/bin/bash

if [ "$1" = "terminator-ea" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300"
fi

if [ "$1" = "terminator-da" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -da 350 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300"
fi

if [ "$1" = "templateBenchmark" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 120 "$2" \
 "BuchiAutomizer.xml;BuchiAutomizerC.xml;buchiAutomizer/templateBenchmarkRcfgLBE.epf"
fi

if [ "$1" = "terminator2" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/eagerNondeterminism"
fi

if [ "$1" = "terminator3" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/ignoreDownStates"
fi

if [ "$1" = "terminator4" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/withoutBouncer"
fi

if [ "$1" = "defaultTest" ]; then
echo "specified folder in default Test setting"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 20 $2 \
"AutomizerBoogie.xml;AutomizerC.xml;hoare10.epf"
fi


if [ "$1" = "determinization" ]; then
echo "test trace abstraction with different determinizations"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -da 20 $2 \
"AutomizerBoogie.xml;AutomizerC.xml;determinization/eagerpost.settings" \
"AutomizerBoogie.xml;AutomizerC.xml;determinization/lazypost.settings" \
"AutomizerBoogie.xml;AutomizerC.xml;determinization/newEager.settings" \
"AutomizerBoogie.xml;AutomizerC.xml;determinization/strongestpost.settings"
fi


if [ "$1" = "svcompMatthiasSafetyBench1" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -da 90 $2 \
"AutomizerBoogie.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl" \
"AutomizerBoogie.xml;AutomizerC.xml;AutomizerSvcompSafety1MinuteSeq.bpl"
fi

if [ "$1" = "svcompMatthiasSafetyBench1LBE" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -da 90 $2 \
"AutomizerBoogie.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl"
fi


if [ "$1" = "svcompAlex" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 $2 \
"Kojak.xml;KojakC.xml;AlexSVCOMP"
fi

if [ "$1" = "svcompMatthias" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/TraceAbstractionTestDir.sh -ea 20 $2 \
"AutomizerBoogie.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl"
fi


if [ "$1" = "0" ]; then
echo "testing minitests"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs/minitests/quantifier \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-simpleTest-SVCOMP"
fi


if [ "$1" = "1" ]; then
echo "testing our example programs with different block encodings"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs/minitests \
"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-EagerPost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-EagerPost-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-Lazypost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-Lazypost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-Lazypost-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-StrongestPost-Hoare" \
"TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-StrongestPost-Hoare"
fi



if [ "$1" = "2" ]; then
echo "small test"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
 "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-EagerPost-Hoare"
fi

if [ "$1" = "3" ]; then
echo "testing TraceCheckerSpWp"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs \
"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp" \
"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare"
fi

if [ "$1" = "4" ]; then
echo "testing TraceCheckerSpWp for SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/systemc \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/programs \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
fi


if [ "$1" = "5" ]; then
echo "testing different interpolations"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-Hoare" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-Hoare"
fi

if [ "$1" = "6" ]; then
echo "testing different interpolations on SV-COMP examples"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/svcomp/ssh-simplified/ \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/svcomp/ntdrivers-simplified \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/svcomp/systemc \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/programs \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
fi


if [ "$1" = "7" ]; then
echo "testing SmtInterpol vs. Z3 on SV-COMP examples"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/c/ssh-simplified/ \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/c/ntdrivers-simplified \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/c/systemc \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 trunk/examples/programs \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBoogie.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
fi


if [ "$1" = "buchiAutomizer0" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 120 "$2" \
 "BuchiAutomizerWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;BuchiAutomizer/BuchiAutomizerBE"
fi

if [ "$1" = "buchiAutomizer1" ]; then
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/rank \
 "BuchiAutomizer.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/programs \
 "BuchiAutomizer.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/terminator \
 "BuchiAutomizer.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/TraceAbstractionTestDir.sh 20 trunk/examples/svcomp \
 "BuchiAutomizer.xml;BuchiAutomizerC.xml;BuchiAutomizer"
fi


#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/systemc \
#"AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-StrongestMinimize" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-EagerMinimize" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LazyMinimize" \

#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 

# trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"


#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy"
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 
#trunk/examples/toolchains/TraceAbstractionTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBoogie.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "TraceAbstractionWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 


