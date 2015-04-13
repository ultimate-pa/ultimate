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
	
	// sorted by line count in ascending order
	private static final String[] m_FILES = {
		//"examples/svcomp/loop-acceleration/diamond_true-unreach-call2.c", // already fails without inlining
		"examples/svcomp/list-properties/simple_true-unreach-call.i",
		"examples/svcomp/list-properties/list_flag_true-unreach-call.i",
		"examples/svcomp/list-properties/alternating_list_true-unreach-call.i",
		"examples/svcomp/list-properties/splice_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/merge_sort_true-unreach-call.i",
		"examples/svcomp/list-properties/list_search_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/bubble_sort_linux_true-unreach-call.i",
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

