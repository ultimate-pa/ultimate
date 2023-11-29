#!/bin/bash

# This script can be used to run individual unit tests from the command line,
# without the complex steps performed by maven for each run.
#
# This requires the JUnit console runner, which can e.g. be downloaded from
# https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/
# Place it in this directory and, if necessary, adjust the variable JUNIT_JAR below.
#
# Execute ./makeFresh.sh first, and then invoke this script as follows:
#
#  > ./run-test.sh <PROJECT> <CLASS> <TEST>
#
# where <PROJECT> is the Ultimate project where the test is located (e.g. "Library-TraceCheckerUtilsTest"),
# <CLASS> is the fully qualified name of the class (e.g. "de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.PetriOwickiGriesTestSuite"),
# and <TEST> is the name of the test case (i.e., method) that you want to run.
# In the case where the tests in <CLASS> are generated dynamically from files,
# make sure to replace any symbols not allowed in method names (e.g. "."),
# and use the resulting name of the test case (e.g. "test_ats" instead of "test.ats").

JUNIT_JAR="junit-platform-console-standalone-1.9.3.jar"

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

PROJECT=$1
CLASS=$2
FILE=$3

cd "$SCRIPT_DIR/../../trunk/source/$PROJECT"

METHOD=$(echo "$FILE" | tr . _)

PATH="$PATH:$SCRIPT_DIR/adds" java -ea -jar "$JUNIT_JAR" \
-cp "$SCRIPT_DIR/../../trunk/source/AbstractInterpretationV2/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/AbstractInterpretationV2Test/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ACSLParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ASTBuilder/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/AutomataScriptInterpreter/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/AutomataScriptParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/AutomatonDeltaDebugger/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BlockEncoding/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BlockEncodingV2/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogieModSetAnnotator/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogiePLParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogiePreprocessor/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogiePreprocessorTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogiePrinter/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BoogieProcedureInliner/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BuchiAutomizer/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/BuchiProgramProduct/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CACSL2BoogieTranslator/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CDTParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CDTPlugin/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ChcSmtPrinter/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ChcSolver/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ChcToBoogie/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CodeCheck/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CoreRCP/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/CoreRCPTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Crocotta/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/GUIGeneratedPreferencePages/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/GUILoggingWindow/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/GuiRCP/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/HornVerifier/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/IcfgToChc/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/IcfgTransformation/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/InvariantSynthesis/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/IRSDependencies/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/JavaCup/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/JungVisualization/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/LassoRanker/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-AcceleratedInterpolation/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-ApacheCommonsCLI/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-Automata/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-AutomataTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-BoogieAST/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-CHC/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-IcfgTransformer/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-IcfgTransformerTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-JavaBDD/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-LassoRanker/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-MCR/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-ModelCheckerUtils/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-ModelCheckerUtilsTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-MSOD/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-MSODTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-PathExpressions/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-PathExpressionsTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-PDR/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-PEA/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-PreferenceJson/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-Sifa/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-SifaTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-SMTLIB/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-SMTLIBTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-SmtLibUtils/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-srParse/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-srParseTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-TraceCheckerUtils/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-TraceCheckerUtilsTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateCore/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateModel/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateTestTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateUtil/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Library-UltimateUtilTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/LTL2aut/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/PeaExampleGenerator/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/PEAtoBoogie/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/PEAtoBoogieTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/RCFGBuilder/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ReachingDefinitions/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Referee/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ReqParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ReqPrinter/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/ReqToTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/Sifa/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SMTInterpol/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SMTInterpolTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SmtParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SMTSolverBridge/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SMTSolverBridgeTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SpaceExParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SpaceExParserTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/SyntaxChecker/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/TraceAbstractionConcurrent/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/TraceAbstraction/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/TraceAbstractionWithAFAs/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/TreeAutomizer/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/UltimateCLI/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/UltimateDeltaDebugger/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/UltimateEliminatorController/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/UltimateRegressionTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/UltimateTest/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/WebBackend/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/WebInterface/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/WitnessParser/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/WitnessPrinter/target/classes" \
-cp "$SCRIPT_DIR/../../trunk/source/.metadata/.plugins/org.eclipse.pde.core/.bundle_pool/plugins/org.apache.commons.io_2.6.0.v20190123-2029.jar" \
--select-method "$CLASS#$METHOD"

