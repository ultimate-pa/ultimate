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
		"examples/termination/TermCompOfficialBenchmarkSet/ultimate"
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 10000;

//	private static final boolean s_Boogie_TreeInterpolants = true;
//	private static final boolean s_C_TreeInterpolants = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
			"BuchiAutomizerBplWithBlockEncoding.xml",
			"buchiAutomizerTestSuite/staged300-SMTInterpol.epf",
		    m_Directories,
		    new String[] {".bpl"},
		    m_Timeout);
		addTestCases(
				"BuchiAutomizerCWithBlockEncoding.xml",
				"buchiAutomizerTestSuite/staged300-SMTInterpol.epf",
			    m_Directories,
			    new String[] {".c"},
			    m_Timeout);
		return super.createTestCases();
	}
}
