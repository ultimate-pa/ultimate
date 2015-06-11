/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for the two interpolation techniques "ForwardPredicates" and 
 * "BackwardPredicates".
 * @author musab@informatik.uni-freiburg.de, heizmanninformatik.uni-freiburg.de
 *
 */

public class ForwardBackwardTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
		"examples/programs/recursivePrograms",
		"examples/programs/toy"
	};
	
	private static final boolean m_TraceAbstractionBoogieWithBackwardPredicates = !true;
	private static final boolean m_TraceAbstractionBoogieWithForwardPredicates = !true;
	private static final boolean m_TraceAbstractionBoogieWithFPandBP = true;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = !true;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = !true;		
	private static final boolean m_TraceAbstractionCWithFPandBP = true;

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionBoogieWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"});
		} 
		if (m_TraceAbstractionBoogieWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"});
		}
		if (m_TraceAbstractionBoogieWithFPandBP) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/ForwardPredicatesAndBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"});
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/BackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		if (m_TraceAbstractionCWithFPandBP) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicatesAndBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}

	
}
