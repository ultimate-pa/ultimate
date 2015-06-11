/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Memsafety extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
		"examples/svcomp/memsafety",
		"examples/svcomp/memsafety-ext",
		"examples/svcomp/list-ext-properties",
		"examples/svcomp/memory-alloca/"
		};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean m_AutomizerWithForwardPredicates = true;
	private static final boolean m_AutomizerWithBackwardPredicates = !true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompMemsafety.epf",
				    m_Directories,
				    new String[] {".i"});
		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompMemsafetyConservative.epf",
				    m_Directories,
				    new String[] {".i"});
		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyLbe.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyLbeConservative.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerCWithBlockEncoding.xml",
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf",
				    m_Directories,
				    new String[] {".i"});
		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCases(
					"AutomizerCWithBlockEncoding.xml",
					"automizer/ForwardPredicates_SvcompMemsafetySeqbeConservative.epf",
				    m_Directories,
				    new String[] {".i"});
		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyAdditionalAssume.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
		if (m_AutomizerWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"automizer/BackwardPredicates_SvcompMemsafety.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}
}
