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
public class Svcomp_Termination extends AbstractBuchiAutomizerTestSuite {
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs = {

//		/*** Category 12. Termination ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }) ,
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}


	private static final boolean s_UseTasimp = true;
	private static final String s_TasimpSetting = "buchiAutomizer/staged300Forward-Z3-Tasimp.epf";
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_UseTasimp) {
			addTestCases("BuchiAutomizerCWithBlockEncoding.xml", 
					s_TasimpSetting, 
					m_DirectoryFileEndingsPairs);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
