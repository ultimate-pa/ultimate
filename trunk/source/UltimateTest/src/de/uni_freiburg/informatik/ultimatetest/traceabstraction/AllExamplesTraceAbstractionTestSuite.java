/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AllExamplesTraceAbstractionTestSuite extends
		AbstractTraceAbstractionTestSuite {
	private static final String m_Path = "examples/programs/";
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;

	private static final boolean m_TraceAbstractionWithForwardPredicates = false;
	private static final boolean m_TraceAbstractionWithBackwardPredicates = !false;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = false;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = !false;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"settingsForwardPredicates",
				    m_Path,
				    new String[] {".bpl"},
				    "Trace Abstraction via Forward Predicates (SP)",
				    "BoogieFilesForwardPredicates",
				    m_Timeout);
		} 
		if (m_TraceAbstractionWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"settingsBackwardPredicates",
				    m_Path,
				    new String[] {".bpl"},
				    "Trace Abstraction via Backward Predicates (WP)",
				    "BoogieFilesBackwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"settingsForwardPredicates.epf",
				    m_Path,
				    new String[] {".c", ".i"},
				    "Trace Abstraction via Forward Predicates (SP)",
				    "CFilesForwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"settingsBackwardPredicates.epf",
				    m_Path,
				    new String[] {".c", ".i"},
				    "Trace Abstraction via Backward Predicates (WP)",
				    "CFilesBackwardPredicates",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
