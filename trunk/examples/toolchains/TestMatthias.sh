#!/bin/bash

if [ "$1" = "terminator-ea" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300-Z3.epf"
fi

if [ "$1" = "terminator-da" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -da 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300-SMTInterpol.epf"
fi

if [ "$1" = "buchiForward-da" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3.epf"
fi

if [ "$1" = "buchiForward-ea" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3.epf"
fi



if [ "$1" = "buchiForward-da-Tasimp" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3-Tasimp.epf"
fi

if [ "$1" = "buchiForward-ea-Tasimp" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3-Tasimp.epf"
fi



if [ "$1" = "MemsafeDerefOnly-ea" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 1900 "$2" \
 "AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_MemsafeDerefOnly_60.epf"
fi

if [ "$1" = "MemsafeDerefOnly-da" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 1900 "$2" \
 "AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_MemsafeDerefOnly_60.epf"
fi

if [ "$1" = "buchiForwardSimplifyComp-da" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 1900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3.epf" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/staged300Forward-Z3-Tasimp.epf"
fi


if [ "$1" = "svcompSimple" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ssh/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ntdrivers/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-consumption/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-commit-tester/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-linux-3.7.3/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-linux-3.4-simple/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-linux-3.0/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf"
fi


if [ "$1" = "svcompPrecise" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/heap-manipulation/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/heap-manipulation/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/list-properties/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/list-properties/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-regression/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ldv-regression/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ddv-machzwd/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachPreciseMM.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/ddv-machzwd/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompReachPreciseMM.epf"
fi


if [ "$1" = "svcompMemsafety" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memsafety/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memsafety/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memsafety-ext/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memsafety-ext/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memory-alloca/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memory-alloca/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memory-unsafe/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompMemsafety.epf"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 \
trunk/examples/svcomp/memory-unsafe/ \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_SvcompMemsafety.epf"
fi




if [ "$1" = "unsatCore" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 600 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/unsatCore/ForwardPredicates.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/unsatCore/ForwardPredicates_WithoutUnsatCore.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/unsatCore/BackwardPredicates.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/unsatCore/BackwardPredicates_WithoutUnsatCore.epf"
fi

if [ "$1" = "3interpol" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 600 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/3interpol/TreeInterpolation.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/3interpol/ForwardPredicates.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/3interpol/BackwardPredicates.epf"
fi



if [ "$1" = "templateBenchmark" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 900 "$2" \
 "BuchiAutomizerBpl.xml;BuchiAutomizerC.xml;buchiAutomizer/templateBenchmark.epf"
fi

if [ "$1" = "templateBenchmarkLBE" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/templateBenchmarkLBE.epf"
fi

if [ "$1" = "dumpLinearLassoRankerScripts" ]; then
echo "dumpLinearLassoRankerScripts for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -da 900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/dumpLinearLassoRankerScripts.epf"
fi


if [ "$1" = "dumpNonlinearLassoRankerScripts" ]; then
echo "dumpNonlinearLassoRankerScripts for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -da 900 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/dumpNonlinearLassoRankerScripts.epf"
fi

if [ "$1" = "dumpAutomizerAUFLIRAScripts" ]; then
echo "$1 for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -da 900 "$2" \
 "AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_Svcomp_300_dumpAUFLIRA.epf"
fi



if [ "$1" = "interpolation" ]; then
echo "testing different interpolation techniques"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 20 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/TreeInterpolants.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates.epf"
fi


if [ "$1" = "testForwardBackward" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 30 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates.epf"
fi


if [ "$1" = "svcompForwardBackward" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 360 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_Svcomp_300.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/BackwardPredicates_Svcomp_300.epf" 
fi


if [ "$1" = "svcompForwardIncrementallyBenchmark" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -da 300 "$2" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/ForwardPredicates_SvcompReachSimpleMM_AssertIncrementally.epf" 
fi


if [ "$1" = "terminator2" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/eagerNondeterminism"
fi

if [ "$1" = "terminator3" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/ignoreDownStates"
fi

if [ "$1" = "terminator4" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 120 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;buchiAutomizer/withoutBouncer"
fi

if [ "$1" = "defaultTest" ]; then
echo "specified folder in default Test setting"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 20 $2 \
"AutomizerBpl.xml;AutomizerC.xml;hoare10.epf"
fi

if [ "$1" = "totalinterpolation" ]; then
echo "$1"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 20 $2 \
"AutomizerBpl.xml;AutomizerC.xml;automizer/TreeInterpolants.epf" \
"AutomizerBpl.xml;AutomizerC.xml;automizer/TreeInterpolants_TotalInterpolation.epf"
fi

if [ "$1" = "bellwald" ]; then
echo "test trace abstraction with new determinization"
trunk/examples/toolchains/AutomizerTestDir.sh -da 120 $2 \
"AutomizerBpl.xml;AutomizerC.xml;SvcompBellwald.epf" \
"AutomizerBpl.xml;AutomizerC.xml;SvcompStrongest.epf"
fi


if [ "$1" = "determinization" ]; then
echo "test trace abstraction with different determinizations"
trunk/examples/toolchains/AutomizerTestDir.sh -da 20 $2 \
"AutomizerBpl.xml;AutomizerC.xml;determinization/eagerpost.settings" \
"AutomizerBpl.xml;AutomizerC.xml;determinization/lazypost.settings" \
"AutomizerBpl.xml;AutomizerC.xml;determinization/newEager.settings" \
"AutomizerBpl.xml;AutomizerC.xml;determinization/strongestpost.settings"
fi


if [ "$1" = "svcompMatthiasSafetyBench1" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/AutomizerTestDir.sh -da 90 $2 \
"AutomizerBpl.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl" \
"AutomizerBpl.xml;AutomizerC.xml;AutomizerSvcompSafety1MinuteSeq.bpl"
fi

if [ "$1" = "svcompMatthiasSafetyBench1LBE" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/AutomizerTestDir.sh -da 90 $2 \
"AutomizerBpl.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl"
fi


if [ "$1" = "svcompAlex" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/AutomizerTestDir.sh 20 $2 \
"Kojak.xml;KojakC.xml;AlexSVCOMP"
fi

if [ "$1" = "svcompMatthias" ]; then
echo "specified folder in a test setting"
trunk/examples/toolchains/AutomizerTestDir.sh -ea 20 $2 \
"AutomizerBpl.xml;AutomizerC.xml;AutomizerSvcompSafety1Minute.bpl"
fi


if [ "$1" = "0" ]; then
echo "testing minitests"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs/minitests/quantifier \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-simpleTest-SVCOMP"
fi


if [ "$1" = "1" ]; then
echo "testing our example programs with different block encodings"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs/minitests \
"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-EagerPost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-EagerPost-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-Lazypost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-Lazypost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-Lazypost-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-StrongestPost-Hoare" \
"AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncodingNoParallel-StrongestPost-Hoare"
fi



if [ "$1" = "2" ]; then
echo "small test"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-EagerPost-Hoare" \
 "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-BlockEncoding-EagerPost-Hoare"
fi





if [ "$1" = "3" ]; then
echo "testing TraceCheckerSpWp"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs \
"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp" \
"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare"
fi

if [ "$1" = "4" ]; then
echo "testing TraceCheckerSpWp for SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/systemc \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/programs \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SpWp-SVCOMP" \
 "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-LargeStatements-StrongestPost-Hoare-SVCOMP" 
fi


if [ "$1" = "5" ]; then
echo "testing different interpolations"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-Hoare" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-Hoare"
fi

if [ "$1" = "6" ]; then
echo "testing different interpolations on SV-COMP examples"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/svcomp/ssh-simplified/ \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/svcomp/ntdrivers-simplified \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/svcomp/systemc \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/programs \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeSeq-ForwardPredicates-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Nested-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-Tree-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-MlbeLoop-ForwardPredicates-SVCOMP"
fi


if [ "$1" = "7" ]; then
echo "testing SmtInterpol vs. Z3 on SV-COMP examples"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/c/ssh-simplified/ \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/c/ntdrivers-simplified \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/c/systemc \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
trunk/examples/toolchains/AutomizerTestDir.sh 120 trunk/examples/programs \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-SmtInterpol-SVCOMP" \
"AutomizerBpl.xml;AutomizerC.xml;Automizer-UnsatCoreSmtInterpolZ3/Automizer-MlbeLoop-ForwardPredicates-Z3-SVCOMP"
fi


if [ "$1" = "buchiAutomizer0" ]; then
echo "buchiAutomizer for folder $2"
trunk/examples/toolchains/AutomizerTestDir.sh 120 "$2" \
 "BuchiAutomizerBplWithBlockEncoding.xml;BuchiAutomizerCWithBlockEncoding.xml;BuchiAutomizer/BuchiAutomizerBE"
fi

if [ "$1" = "buchiAutomizer1" ]; then
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/rank \
 "BuchiAutomizerBpl.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/programs \
 "BuchiAutomizerBpl.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/terminator \
 "BuchiAutomizerBpl.xml;BuchiAutomizerC.xml;BuchiAutomizer"
trunk/examples/toolchains/AutomizerTestDir.sh 20 trunk/examples/svcomp \
 "BuchiAutomizerBpl.xml;BuchiAutomizerC.xml;BuchiAutomizer"
fi


#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/systemc \
#"AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-StrongestMinimize" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-EagerMinimize" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LazyMinimize" \

#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" 

# trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"
# trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongestMinimizeSevpa"


#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ssh-simplified/ \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/ntdrivers-simplified \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy"
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/svcomp/systemc \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 
#trunk/examples/toolchains/AutomizerTestDir.sh 1000 trunk/examples/programs \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeStrongest" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingStrongest" \
# "AutomizerBpl.xml;AutomizerC.xml;TraceAbstraction-svcomp-LargeLazy" \
# "AutomizerBplWithBlockEncoding.xml;TraceAbstractionCWithBlockEncoding.xml;TraceAbstraction-svcomp-BlockEncodingLazy" 


