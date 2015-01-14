/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for the different versions of incremental inclusion
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class IncrementalInclusionTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Programs = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
//		"examples/programs/toy",
		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
	};
	
	private static final String[] m_Settings = {
		"automizer/incrementalInclusion/Difference.epf",
		"automizer/incrementalInclusion/IncrementalInclusionViaDifference.epf",
		"automizer/incrementalInclusion/IncrementalInclusion2.epf",
		"automizer/incrementalInclusion/IncrementalInclusion3.epf",
		"automizer/incrementalInclusion/IncrementalInclusion4.epf",
		"automizer/incrementalInclusion/IncrementalInclusion5.epf",
	};
	
	private static final boolean m_Boogie = true;
	private static final boolean m_C = !true;

	// Time out for each test case in milliseconds
	private final static int m_Timeout = 10 * 1000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			if (m_Boogie) {
				addTestCases(
						"AutomizerBpl.xml",
						setting,
						m_Programs,
						new String[] {".bpl"},
						m_Timeout);
			}
			if (m_C) {
				addTestCases(
						"AutomizerC.xml",
						setting,
						m_Programs,
						new String[] {".c", ".i"},
						m_Timeout);
			}
		}
		return super.createTestCases();
	}

	
}
