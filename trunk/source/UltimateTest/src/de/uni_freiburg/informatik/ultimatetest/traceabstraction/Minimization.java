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
public class Minimization extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
//		"examples/programs/regression", 
		"examples/svcomp/recursive/",
		};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean s_Boogie_TreeInterpolants_MinimizeSevpa = true;
	private static final boolean s_C_TreeInterpolants_MinimizeSevpa = true;
	private static final boolean s_Boogie_TreeInterpolants_ShrinkNwa = true;
	private static final boolean s_C_TreeInterpolants_ShrinkNwa = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants_MinimizeSevpa) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"});
		} 
		if (s_C_TreeInterpolants_MinimizeSevpa) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		
		if (s_Boogie_TreeInterpolants_ShrinkNwa) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants_ShrinkNwa.epf",
				    m_Directories,
				    new String[] {".bpl"});
		} 
		if (s_C_TreeInterpolants_ShrinkNwa) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/TreeInterpolants_ShrinkNwa.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}
}
