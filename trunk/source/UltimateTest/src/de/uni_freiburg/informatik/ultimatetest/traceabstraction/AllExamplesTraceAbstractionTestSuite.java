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
	
	// Time out for each test case in seconds
	private static int m_Timeout = 20;

	private static final boolean m_TraceAbstractionWithForwardPredicates = false;
	private static final boolean m_TraceAbstractionWithBackwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = false;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionWithForwardPredicates) {
			addTestCases(
					"TraceAbstraction.xml",
					"settingsForwardPredicates",
				    m_Path,
				    new String[] {".bpl"},
				    "TraceAbstraction via Forward Predicates (SP)",
				    m_Timeout);
		} 
		if (m_TraceAbstractionWithBackwardPredicates) {
			addTestCases(
					"TraceAbstraction.xml",
					"settingsBackwardPredicates",
				    m_Path,
				    new String[] {".bpl"},
				    "TraceAbstraction via Backward Predicates (WP)",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"TraceAbstractionC.xml",
					"settingsForwardPredicates",
				    m_Path,
				    new String[] {".c", ".i"},
				    "TraceAbstraction via Forward Predicates (SP)",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"TraceAbstractionC.xml",
					"settingsBackwardPredicates",
				    m_Path,
				    new String[] {".c", ".i"},
				    "TraceAbstraction via Backward Predicates (WP)",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
