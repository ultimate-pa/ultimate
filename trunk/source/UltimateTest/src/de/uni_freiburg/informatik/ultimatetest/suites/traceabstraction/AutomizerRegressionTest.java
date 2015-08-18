/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractModelCheckerTestSuite.DirectoryFileEndingsPair;

/**
 * Test small examples on our two most common settings.
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class AutomizerRegressionTest extends AbstractTraceAbstractionTestSuite {
	
	private static final String[] m_UltimateRepository_ForwardPredicates = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};
	
	private static final String[] m_UltimateRepository_TreeInterpolation = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};

	
	
	private static final String[] m_Settings_ForwardPredicates = {
		"automizer/ForwardPredicates.epf",
	};
	
	private static final String[] m_Settings_TreeInterpolation = {
		"automizer/TreeInterpolants.epf",
	};

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}
	
	private static final String[] m_BoogieToolchains = {
//		"AutomizerBpl.xml",
//		"AutomizerBplWithBlockEncoding.xml",
//		"AutomizerBplInline.xml",
	};
	
	private static final String[] m_CToolchains = {
		"AutomizerC.xml",
//		"AutomizerCWithBlockEncoding.xml",
//		"AutomizerCInline.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		{
			// Tests with TreeInterpolation
			for (String setting : m_Settings_TreeInterpolation) {
				for (String toolchain : m_BoogieToolchains) {
					addTestCases(toolchain, setting, m_UltimateRepository_TreeInterpolation, 
							new String[] {".bpl"});
				}
			}
			for (String setting : m_Settings_TreeInterpolation) {
				for (String toolchain : m_CToolchains) {
					addTestCases(toolchain, setting, m_UltimateRepository_TreeInterpolation, 
							new String[] {".c", ".i"});
				}
			}
		}
		
		{	// Tests with ForwardPredicates
			for (String setting : m_Settings_ForwardPredicates) {
				for (String toolchain : m_BoogieToolchains) {
					addTestCases(toolchain, setting, m_UltimateRepository_ForwardPredicates, 
							new String[] {".bpl"});
				}
			}
			for (String setting : m_Settings_ForwardPredicates) {
				for (String toolchain : m_CToolchains) {
					addTestCases(toolchain, setting, m_UltimateRepository_ForwardPredicates, 
							new String[] {".c", ".i"});
				}
			}
		}
		return super.createTestCases();
	}

	
}
