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
public class QuantifierFolderTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String m_Path = "examples/programs/quantifier";
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 5000;

	private static final boolean s_Boogie = true;
	private static final boolean s_C = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie) {
			addTestCases(
					"AutomizerBpl.xml",
					"memSafety.epf",
				    m_Path,
				    new String[] {".bpl"},
				    "Automizer via ForwardPredicates",
				    "Boogie",
				    m_Timeout);
		} 
		if (s_C) {
			addTestCases(
					"AutomizerC.xml",
					"memSafety.epf",
				    m_Path,
				    new String[] {".c", ".i"},
				    "Automizer via ForwardPredicates",
				    "C",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
