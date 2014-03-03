#!/bin/bash
echo "building UltimateSources.tar.bz2 which contains the sources of all public plugins"
echo "!!! Warning !!! Use this script only on a clean checkout. Otherwise a lot of .class files are included"
tar cjf UltimateSources.tar.bz2 \
../../trunk/source/ACSLParser \
../../trunk/source/ASTBuilder \
../../trunk/source/AutomataScriptInterpreter \
../../trunk/source/AutomataScriptParser \
../../trunk/source/BlockEncoding \
../../trunk/source/BoogiePLParser \
../../trunk/source/BoogiePreprocessor \
../../trunk/source/BoogiePreprocessorTest \
../../trunk/source/BoogiePrinter \
../../trunk/source/BuchiAutomizer \
../../trunk/source/CACSL2BoogieTranslator \
../../trunk/source/CDTParser \
../../trunk/source/CDTPlugin \
../../trunk/source/CodeCheck \
../../trunk/source/CoreRCP \
../../trunk/source/CoreRCPTest \
../../trunk/source/JavaCup \
../../trunk/source/LassoRanker \
../../trunk/source/Library-LassoRanker \
../../trunk/source/Library-ModelCheckerUtils \
../../trunk/source/Library-SMTLIB \
../../trunk/source/Library-UltimateTest \
../../trunk/source/Library-UltimateUtil \
../../trunk/source/Library-UltimateUtilTest \
../../trunk/source/Library-junit-helper \
../../trunk/source/Library-log4j \
../../trunk/source/NestedWordAutomata \
../../trunk/source/RCFGBuilder \
../../trunk/source/RankingFunctions \
../../trunk/source/SMTInterpol \
../../trunk/source/SMTSolverBridge \
../../trunk/source/TraceAbstraction \
../../trunk/source/TraceAbstractionConcurrent \
../../trunk/source/UltimateRegressionTest \
../../trunk/source/UltimateTest



