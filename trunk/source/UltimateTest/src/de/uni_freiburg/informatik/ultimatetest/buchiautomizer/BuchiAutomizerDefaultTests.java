/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiAutomizerDefaultTests extends
		AbstractBuchiAutomizerTestSuite {
	private static final String[] m_Directories = {
//		"examples/lassos",
		"examples/termination/svcomp-sorted/",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 150 * 1000;

	private static final boolean s_UseMediumBlockEncoding = false;
	private static final String s_MediumBlockEncodingSetting = "buchiAutomizer/staged300Forward-Z3.epf";

	private static final boolean s_UseLargeBlockEncoding = false;
	private static final String s_LargeBlockEncodingSetting = "buchiAutomizer/staged300Forward-Z3-LBE.epf";
	
	private static final boolean s_UseTasimp = true;
	private static final String s_TasimpSetting = "buchiAutomizer/staged300Forward-Z3-Tasimp.epf";
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_UseMediumBlockEncoding) {
			addTestCases(
					"BuchiAutomizerBplWithBlockEncoding.xml",
					s_MediumBlockEncodingSetting,
					m_Directories,
					new String[] {".bpl"},
					m_Timeout);
			addTestCases(
					"BuchiAutomizerCWithBlockEncoding.xml",
					s_MediumBlockEncodingSetting,
					m_Directories,
					new String[] {".c"},
					m_Timeout);
		}
		if (s_UseLargeBlockEncoding) {
			addTestCases(
					"BuchiAutomizerBplWithBlockEncoding.xml",
					s_LargeBlockEncodingSetting,
					m_Directories,
					new String[] {".bpl"},
					m_Timeout);
			addTestCases(
					"BuchiAutomizerCWithBlockEncoding.xml",
					s_LargeBlockEncodingSetting,
					m_Directories,
					new String[] {".c"},
					m_Timeout);
		}
		if (s_UseTasimp) {
			addTestCases(
					"BuchiAutomizerBplWithBlockEncoding.xml",
					s_TasimpSetting,
					m_Directories,
					new String[] {".bpl"},
					m_Timeout);
			addTestCases(
					"BuchiAutomizerCWithBlockEncoding.xml",
					s_TasimpSetting,
					m_Directories,
					new String[] {".c"},
					m_Timeout);
		}
		return super.createTestCases();
	}
}
