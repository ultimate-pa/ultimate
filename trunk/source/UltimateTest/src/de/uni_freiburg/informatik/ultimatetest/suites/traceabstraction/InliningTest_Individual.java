package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 *  Represents a subset from {@link InliningTest}, which is currently investigated.
 * 
 * 	@author schaetzc@informatik.uni-freiburg.de
 */
public class InliningTest_Individual extends AbstractTraceAbstractionTestSuite {
	
	/** Tests that pass without inlining, but fail with inlining. */
	private static final String[] sFiles = {
		// passes with z3-v4.3.3, fails with z3-v4.4 due to memory
//		"examples/programs/quantifier/regression/c/Aliasing01-Safe.c",
		
		// AssertionError: "Simplification unsound?"
//		"examples/programs/quantifier/regression/ArrowOperator01-read-Safe.c",
//		"examples/programs/quantifier/regression/ArrowOperator03-write-Safe.c",
//		"examples/programs/quantifier/regression/ArrowOperator06-nested-Safe.c",
//		"examples/programs/quantifier/regression/c/SelfReferencingStruct01-Safe.c",
//
//		// Error: "Neither filename nor path nor first line contains a keyword that defines the expected result"
//		// (Error from above, when #Safe or #Unsafe is added)
//		"examples/programs/quantifier/regression/UnconfirmedAliasingProblem2.c",
//		"examples/programs/quantifier/regression/todo/auxVarType.c",
//		"examples/programs/quantifier/regression/copyStructThatIsOnHeap.c",
		
		// Error in BoogiePreprocessor, regarding quantifiers
//		"examples/BoogiePL/schaetzc/TestMultiQuant.bpl",
		
		// Former problem with requires specifications of main procedures.
		"examples/programs/recursivePrograms/Katharinenberg.bpl",
		"examples/programs/recursivePrograms/Katharinenberg.c",
	};
	
	private static final boolean sTraceAbstractionBoogie = true;
	private static final boolean sTraceAbstractionBoogieInline = true;
	private static final boolean sTraceAbstractionC = true;
	private static final boolean sTraceAbstractionCInline = true;

	@Override
	public long getTimeout() {
		return 12 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String file : sFiles) {
			if (file.matches(".*\\.bpl$")) {
				if (sTraceAbstractionBoogie) {
					addTestCase(
							"AutomizerBpl.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
				if (sTraceAbstractionBoogieInline) {
					addTestCase(
							"AutomizerBplInline.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
			} else if (file.matches(".*\\.[ci]$")) {
				if (sTraceAbstractionC) {
					addTestCase(
							"AutomizerC.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
				if (sTraceAbstractionCInline) {
					addTestCase(
							"AutomizerCInline.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
			}
		}
		return super.createTestCases();
	}

	
}
