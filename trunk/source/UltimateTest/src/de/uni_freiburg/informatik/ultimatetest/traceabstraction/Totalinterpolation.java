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
public class Totalinterpolation extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
//		"examples/programs/regression",
//		"examples/programs/toy",
//		"examples/programs/recursivePrograms",
//		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
//		"examples/programs/reals"
//		"examples/svcomp/ssh-simplified",
		"examples/svcomp/systemc"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 300 * 1000;

	private static final boolean s_Boogie_TreeInterpolants = true;
	private static final boolean s_C_TreeInterpolants = true;
	private static final boolean s_Boogie_TreeInterpolantsWithTotalinterpolation = true;
	private static final boolean s_C_TreeInterpolantsWithTotalinterpolation = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
		} 
		if (s_C_TreeInterpolants) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		
		if (s_Boogie_TreeInterpolantsWithTotalinterpolation) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants_TotalInterpolation.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
		} 
		if (s_C_TreeInterpolantsWithTotalinterpolation) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/TreeInterpolants_TotalInterpolation.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
