/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for array interpolation
 * @author musab@informatik.uni-freiburg.de, heizmanninformatik.uni-freiburg.de
 *
 */

public class ArrayInterplationTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
		"examples/svcomp/ldv-regression/"
	};
	
	private static final boolean m_TraceAbstractionBoogieWithBackwardPredicates = false;
	private static final boolean m_TraceAbstractionBoogieWithForwardPredicates = false;
	private static final boolean m_TraceAbstractionBoogieWithFPandBP = false;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = false;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = true;		
	private static final boolean m_TraceAbstractionCWithFPandBP = false;
	// Time out for each test case in milliseconds
	private final static int m_Timeout = 120 * 1000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionBoogieWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
		} 
		if (m_TraceAbstractionBoogieWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
		}
		if (m_TraceAbstractionBoogieWithFPandBP) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicatesAndBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/arrayInterpolationTest/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithFPandBP) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicatesAndBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		return super.createTestCases();
	}

	
}
