/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class InterpolationTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
		"examples/programs/regression/",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
//		"examples/svcomp/recursive/",
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 10 * 1000;

	private static final boolean s_ForwardPredicates = true;
	private static final boolean s_SMTInterpol = true;
	private static final boolean s_iZ3 = true;
	private static final boolean s_Princess = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_ForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		if (s_SMTInterpol) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/SMTInterpol.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/SMTInterpol.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		} 
		if (s_iZ3) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/iZ3.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/iZ3.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		if (s_Princess) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/Princess.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/Princess.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    m_Timeout);
		} 
		return super.createTestCases();
	}
}
