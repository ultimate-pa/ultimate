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
	private static final String[] m_Directories = { "examples/programs/" };
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;

	private static final boolean m_TraceAbstractionWithForwardPredicates = true;
	private static final boolean m_TraceAbstractionWithBackwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
//				    "Trace Abstraction via Forward Predicates (SP)",
//				    "BoogieFilesForwardPredicates",
				    m_Timeout);
		} 
		if (m_TraceAbstractionWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
//				    "Trace Abstraction via Backward Predicates (WP)",
//				    "BoogieFilesBackwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
//				    "Trace Abstraction via Forward Predicates (SP)",
//				    "CFilesForwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
//				    "Trace Abstraction via Backward Predicates (WP)",
//				    "CFilesBackwardPredicates",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
