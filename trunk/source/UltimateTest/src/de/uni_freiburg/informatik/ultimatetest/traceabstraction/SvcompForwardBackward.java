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
public class SvcompForwardBackward extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { "examples/svcomp/ssh-simplified/" };
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 60000;

	private static final boolean m_TraceAbstractionWithForwardPredicates = true;
	private static final boolean m_TraceAbstractionWithBackwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicates_Svcomp_300.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Trace Abstraction via Forward Predicates (SP)",
				    "BoogieFilesForwardPredicates",
				    m_Timeout);
		} 
		if (m_TraceAbstractionWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/BackwardPredicates_Svcomp_300.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Trace Abstraction via Backward Predicates (WP)",
				    "BoogieFilesBackwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_Svcomp_300.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Trace Abstraction via Forward Predicates (SP)",
				    "CFilesForwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/BackwardPredicates_Svcomp_300.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Trace Abstraction via Backward Predicates (WP)",
				    "CFilesBackwardPredicates",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
