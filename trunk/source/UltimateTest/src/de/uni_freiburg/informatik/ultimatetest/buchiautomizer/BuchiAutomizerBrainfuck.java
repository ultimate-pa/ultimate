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
public class BuchiAutomizerBrainfuck extends
		AbstractBuchiAutomizerTestSuite {
	private static final String[] m_Directories = {
//		"examples/lassos",
//		"examples/termination/svcomp-sorted/success/",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/cooperatingT2/difficult/solved",
//		"examples/termination/cooperatingT2/terminating",
		"examples/termination/Brainfuck/nonterminating",
//		"examples/termination/Brainfuck-terminating",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}
	
	private static final String s_LargeBlockEncodingSetting = "buchiAutomizer/staged300Forward-SMTInterpol-LBE.epf";
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
			"BuchiAutomizerBplWithBlockEncoding.xml",
			s_LargeBlockEncodingSetting,
			m_Directories,
			new String[] {".bpl"});
		return super.createTestCases();
	}
}
