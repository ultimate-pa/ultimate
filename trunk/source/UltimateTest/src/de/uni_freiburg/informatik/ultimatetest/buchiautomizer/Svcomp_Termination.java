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
public class Svcomp_Termination extends AbstractBuchiAutomizerTestSuite {
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs = {

//		/*** Category 12. Termination ***/
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }) ,
	};

	// Time out for each test case in milliseconds
	private static long m_Timeout = 10 * 1000;

	private static final boolean s_UseTasimp = true;
	private static final String s_TasimpSetting = "buchiAutomizer/staged300Forward-Z3-Tasimp.epf";
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_UseTasimp) {
			addTestCases("BuchiAutomizerCWithBlockEncoding.xml", 
					s_TasimpSetting, 
					m_DirectoryFileEndingsPairs,
					m_Timeout);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
