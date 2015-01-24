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
public class NonlinearArithmeticInterpolationTest extends
		AbstractTraceAbstractionTestSuite {
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairsMemsafety = {
		new DirectoryFileEndingsPair("examples/programs/nonlinearArithmetic/memsafety", new String[]{ ".i", ".c" }) ,
	};
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairsReach = {
		new DirectoryFileEndingsPair("examples/programs/nonlinearArithmetic/reach", new String[]{ ".i", ".c" }) ,
	};

	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 900 * 1000;

	private static final boolean m_AutomizerWithForwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/nonlinearArithmetic/svComp-64bit-memsafety-Automizer.epf",
					m_DirectoryFileEndingsPairsMemsafety,
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"automizer/nonlinearArithmetic/svComp-64bit-precise-Automizer.epf",
					m_DirectoryFileEndingsPairsReach,
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
