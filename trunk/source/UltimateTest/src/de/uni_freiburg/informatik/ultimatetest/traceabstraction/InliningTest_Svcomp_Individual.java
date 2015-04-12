package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 *  Test for individual files from SV-COMP.
 *  Represents a subset from {@link InliningTest_Svcomp_Reach_PreciseMemoryModel}, which is currently investigated.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InliningTest_Svcomp_Individual extends AbstractTraceAbstractionTestSuite {
	
	private static final String[] m_FILES = {
		"examples/svcomp/loop-acceleration/diamond_true-unreach-call2.c",
	};

	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean m_AutomizerWithInlining = true;
	private static final boolean m_AutomizerWithoutInlining = false;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String file : m_FILES) {
			if (m_AutomizerWithInlining) {
				addTestCase("AutomizerCInline.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf", file);
			}
			if (m_AutomizerWithoutInlining) {
				addTestCase("AutomizerC.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf",  file);
			}
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

}

