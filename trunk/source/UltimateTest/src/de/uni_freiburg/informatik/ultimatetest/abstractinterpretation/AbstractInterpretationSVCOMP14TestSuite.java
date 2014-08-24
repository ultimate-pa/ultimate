/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationSVCOMP14TestSuite extends
		AbstractAbstractInterpretationTestSuite {
	
	private static final String[] m_Directories = {
		"examples/svcomp/loops/",
		"examples/svcomp/eca/",
		"examples/svcomp/systemc/",
		};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
				"AbstractInterpretationC.xml",
				"AbstractInterpretation.epf",
			    m_Directories,
			    new String[] {".c"},
			    "AI c",
			    "absintsvcomp",
			    m_Timeout,
			    true);
		return Util.firstN(super.createTestCases(), 20);
		//return super.createTestCases();
	}

}
