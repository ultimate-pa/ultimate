/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Reach_SimpleMemoryModel extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
		"examples/svcomp/ldv-linux-3.0/",
		"examples/svcomp/ldv-linux-3.4-simple/",
		"examples/svcomp/ldv-linux-3.7.3/",
		"examples/svcomp/ldv-commit-tester/",
		"examples/svcomp/ldv-consumption/",
		"examples/svcomp/ntdrivers/",
		"examples/svcomp/ssh/"
		};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;

	private static final boolean m_AutomizerWithForwardPredicates = true;
	private static final boolean m_AutomizerWithBackwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/ForwardPredicates_SvcompReachSimpleMM.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Trace Abstraction via Forward Predicates (SP)",
				    "CFilesForwardPredicates",
				    m_Timeout);
		}
//		if (m_AutomizerWithBackwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"traceAbstractionTestSuite/BackwardPredicates.epf",
//				    m_Directories,
//				    new String[] {".c", ".i"},
//				    "traceAbstractionTestSuite/BackwardPredicates.epf",
//				    "CFilesBackwardPredicates",
//				    m_Timeout);
//		}
		return super.createTestCases();
	}
}
