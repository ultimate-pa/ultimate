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
		"examples/programs/regression",
//		"examples/programs/toy",
//		"examples/programs/recursivePrograms",
//		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
//		"examples/programs/reals"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 5000;

	private static final boolean s_Boogie_TreeInterpolants = true;
	private static final boolean s_C_TreeInterpolants = true;
	private static final boolean s_Boogie_TreeInterpolantsWithTotalinterpolation = true;
	private static final boolean s_C_TreeInterpolantsWithTotalinterpolation = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Treeinterpolants",
				    "Boogie",
				    m_Timeout);
		} 
		if (s_C_TreeInterpolants) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Treeinterpolants",
				    "C",
				    m_Timeout);
		}
		
		if (s_Boogie_TreeInterpolantsWithTotalinterpolation) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/TreeInterpolants_TotalInterpolation.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Treeinterpolants with totalinterpolation",
				    "Boogie",
				    m_Timeout);
		} 
		if (s_C_TreeInterpolantsWithTotalinterpolation) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/TreeInterpolants_TotalInterpolation.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Treeinterpolants with totalinterpolation",
				    "C",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
