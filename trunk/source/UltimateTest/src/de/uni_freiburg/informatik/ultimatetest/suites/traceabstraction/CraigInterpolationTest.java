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
public class CraigInterpolationTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
//		"examples/programs/regression",
//		"examples/programs/quantifier",
		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
//		"examples/svcomp/recursive/",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 100 * 1000;
	}

	private static final boolean s_Boogie_TreeInterpolants = true;
	private static final boolean s_C_TreeInterpolants = true;
	private static final boolean s_Boogie_NestedInterpolants = true;
	private static final boolean s_C_NestedInterpolants = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"});
		} 
		if (s_C_TreeInterpolants) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		
		if (s_Boogie_NestedInterpolants) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/NestedInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"});
		} 
		if (s_C_NestedInterpolants) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/NestedInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}
}
