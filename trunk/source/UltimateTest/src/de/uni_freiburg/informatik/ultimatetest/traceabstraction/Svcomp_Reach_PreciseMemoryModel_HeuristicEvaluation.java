/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de, musab@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Reach_PreciseMemoryModel_HeuristicEvaluation extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
//		"examples/svcomp/bitvector/",
//		"examples/svcomp/bitvector-regression/",
//		"examples/svcomp/ntdrivers-simplified/",
//		"examples/svcomp/ssh-simplified/",
//		"examples/svcomp/locks/",
//		"examples/svcomp/eca/",
//		"examples/svcomp/loops/",
//		"examples/svcomp/product-lines/",
//		"examples/svcomp/heap-manipulation/",
//		"examples/svcomp/list-properties/",
//		"examples/svcomp/ldv-regression/",
//		"examples/svcomp/ddv-machzwd/",
//		"examples/svcomp/recursive/",
		"examples/svcomp/systemc/"
//		"examples/svcomp/systemc_OnlyOne/"
//		"examples/svcomp/seq-mthreaded/",
//		"examples/svcomp/seq-pthread/"
		};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 60000;

	private static final boolean m_AutomizerWithForwardPredicates = true;
	private static final boolean m_AutomizerWithBackwardPredicates = !true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		// Heuristic 1 (OUTSIDE_FIRST1)
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic1.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		// Heuristic 2 (OUTSIDE_FIRST2)
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic2.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		// Heuristic 3 (OUTSIDE_FIRST3)
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic3.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		// Heuristic 4 (INSIDE_FIRST1)
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic4.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
						
		if (m_AutomizerWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/BackwardPredicates_SvcompReachPreciseMM.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
//		return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}
}
