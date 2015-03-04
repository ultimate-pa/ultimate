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
	private static final String[] m_Programs = { 
//		"examples/programs/regression",
//		"examples/programs/toy",
//		"examples/programs/recursivePrograms",
//		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
//		"examples/programs/reals"
//		"examples/svcomp/ssh-simplified",
//		"examples/svcomp/systemc"
		"examples/svcomp/eca-rers2012",
	};
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"automizer/totalinterpolation/TreeInterpolants.epf",
//		"automizer/totalinterpolation/TreeInterpolants_Conservative.epf",
		"automizer/totalinterpolation/TreeInterpolants_LBE.epf",
		"automizer/totalinterpolation/TreeInterpolants_TotalInterpolation.epf",
//		"automizer/totalinterpolation/TreeInterpolants_TotalInterpolation_Conservative.epf",
		"automizer/totalinterpolation/TreeInterpolants_TotalInterpolation_LBE.epf",
	};
	
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 5 * 60 * 1000;

	private static final boolean m_Boogie = true;
	private static final boolean m_C = true;
	
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
