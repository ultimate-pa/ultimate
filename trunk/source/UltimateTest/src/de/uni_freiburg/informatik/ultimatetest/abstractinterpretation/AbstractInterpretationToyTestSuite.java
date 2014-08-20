/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Stolen from Svcomp_Reach_PreciseMemoryModel ;-)
 */
public class AbstractInterpretationToyTestSuite extends
		AbstractAbstractInterpretationTestSuite {
	
	private static final String[] m_Directories = {
		//"examples/programs/toy/"
		"examples/programs/regression/bpl/"
		};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
				"AbstractInterpretation.xml",
				"AbstractInterpretation.epf",
			    m_Directories,
			    new String[] {".bpl"},
			    "Abstract interpretation BPL safety check",
			    "absintbplsafetycheck",
			    m_Timeout);
		//return Util.firstN(super.createTestCases(), 30);
		return super.createTestCases();
	}
}
