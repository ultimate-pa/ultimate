/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

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

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 900 * 1000;
	}

	private static final boolean m_AutomizerWithForwardPredicates = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/nonlinearArithmetic/svComp-64bit-memsafety-Automizer.epf",
					m_DirectoryFileEndingsPairsMemsafety);
			addTestCases(
					"AutomizerC.xml",
					"automizer/nonlinearArithmetic/svComp-64bit-precise-Automizer.epf",
					m_DirectoryFileEndingsPairsReach);
		}
		return super.createTestCases();
	}
}
