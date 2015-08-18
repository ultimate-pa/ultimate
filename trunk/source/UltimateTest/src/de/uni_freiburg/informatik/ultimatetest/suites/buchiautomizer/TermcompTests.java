/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TermcompTests extends
		AbstractBuchiAutomizerTestSuite {
	
	
	private static final String[] m_UltimateRepository = {
		"examples/termination/termcomp2015/C/",
		"examples/termination/termcomp2015/C_Integer/Stroeder_15",
		"examples/termination/termcomp2015/C_Integer/Ton_Chanh_15",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}
	
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"buchiAutomizer/termcomp2015_Tests.epf",
	};
	
	
	private static final String[] m_CToolchains = {
		"AutomizerAndBuchiAutomizerCWithBlockEncoding.xml",
//		"BuchiAutomizerCInlineWithBlockEncoding.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}
	
}
