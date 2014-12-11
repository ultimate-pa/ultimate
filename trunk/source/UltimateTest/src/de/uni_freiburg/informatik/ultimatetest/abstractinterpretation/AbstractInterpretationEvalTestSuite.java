/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Stolen from Svcomp_Reach_PreciseMemoryModel ;-)
 */
public class AbstractInterpretationEvalTestSuite extends
		AbstractAbstractInterpretationTestSuite {
	
	private boolean m_compareToAutomizer = !false;
	
	private static final String[] m_directories = {
		/* ULTIMATE repo */
		"examples/programs/regression/bpl/",
		"examples/programs/regression/c/",
		"examples/programs/recursivePrograms",
		/* SV-COMP repo */
		//"examples/svcomp/loops/",			// SPLIT
		//"examples/svcomp/loopsSelection/",
		//"examples/svcomp/eca/",			// SPLIT
		//"examples/svcomp/ecaSelection/",
		//"examples/svcomp/systemc/",		// SPLIT
		//"examples/svcomp/systemc1/",
		//"examples/svcomp/systemc2/",
	};
	
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		// Abstract Interpretation
		addTestCases(
				"AbstractInterpretation.xml",
				"AbstractInterpretation.epf",
				m_directories,
			    new String[] {".bpl"},
			    "AI .bpl",
			    "abstractinterpretationbpl",
			    m_Timeout);
		addTestCases(
				"AbstractInterpretationC.xml",
				"AbstractInterpretation.epf",
				m_directories,
			    new String[] {".c"},
			    "AI .c",
			    "abstractinterpretationc",
			    m_Timeout);
		// Automizer
		if (m_compareToAutomizer) {
			addTestCases(
					"AutomizerBpl.xml",
					"AbstractInterpretation.epf",
					m_directories,
				    new String[] {".bpl"},
				    "AI .bpl",
				    "automizerbpl",
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"AbstractInterpretation.epf",
					m_directories,
				    new String[] {".c"},
				    "AI .c",
				    "automizerc",
				    m_Timeout);
		}
		//return Util.firstN(super.createTestCases(), 20);
		return super.createTestCases();
	}
}
