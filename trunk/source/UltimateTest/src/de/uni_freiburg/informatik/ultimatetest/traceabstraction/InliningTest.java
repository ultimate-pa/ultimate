package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for the inlining of Boogie procedures which in implemented by Claus. 
 * 
 * @author heizmanninformatik.uni-freiburg.de
 */

public class InliningTest extends AbstractTraceAbstractionTestSuite {

	private static final String[] sDirectories = {
		"examples/programs/regression",
		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
		"examples/programs/recursivePrograms",
		"examples/programs/toy",
	};
	
	private static final boolean sTraceAbstractionBoogie = false;
	private static final boolean sTraceAbstractionBoogieInline = true;
	private static final boolean sTraceAbstractionC = false;
	private static final boolean sTraceAbstractionCInline = true;

	@Override
	public long getTimeout() {
		return 12 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (sTraceAbstractionBoogie) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicates.epf",
				    sDirectories,
				    new String[] {".bpl"});
		}
		if (sTraceAbstractionBoogieInline) {
			addTestCases(
					"AutomizerBplInline.xml",
					"automizer/ForwardPredicates.epf",
				    sDirectories,
				    new String[] {".bpl"});
		}
		if (sTraceAbstractionC) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates.epf",
				    sDirectories,
				    new String[] {".c", ".i"});
		}
		if (sTraceAbstractionCInline) {
			addTestCases(
					"AutomizerCInline.xml",
					"automizer/ForwardPredicates.epf",
				    sDirectories,
				    new String[] {".c", ".i"});
		} 
		return super.createTestCases();
	}

	
}
