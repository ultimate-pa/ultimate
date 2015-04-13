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
	
	/** Files to be tested. */
	private static final String[] m_FILES = {
		// Failed test from before fix of "old(vars) only assigned on first call".
		// Sorted by line count in ascending order
		/*
		"examples/svcomp/list-properties/simple_true-unreach-call.i",
		"examples/svcomp/list-properties/list_flag_true-unreach-call.i",
		"examples/svcomp/list-properties/alternating_list_true-unreach-call.i",
		"examples/svcomp/list-properties/splice_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/merge_sort_true-unreach-call.i",
		"examples/svcomp/list-properties/list_search_true-unreach-call.i",
		"examples/svcomp/heap-manipulation/bubble_sort_linux_true-unreach-call.i",
		*/
		// Failed tests from after fix of "old(vars) only assigned on first call".
		"examples/svcomp/loop-acceleration/diamond_true-unreach-call2.c",
		"examples/svcomp/loop-lit/afnp2014_true-unreach-call.c",
		"examples/svcomp/loop-lit/bhmr2007_true-unreach-call.c.i",
		"examples/svcomp/loop-lit/cggmp2005_true-unreach-call.c",
		"examples/svcomp/loop-lit/cggmp2005_variant_true-unreach-call.c.i",
		"examples/svcomp/loop-lit/css2003_true-unreach-call.c",
		"examples/svcomp/loop-lit/gj2007_true-unreach-call.c",
		"examples/svcomp/loop-lit/gsv2008_true-unreach-call.c",
		"examples/svcomp/loop-lit/mcmillan2006_true-unreach-call.c",
		"examples/svcomp/loops/bubble_sort_true-unreach-call.i",
		"examples/svcomp/loops/linear_sea.ch_true-unreach-call.i",
		"examples/svcomp/loops/linear_search_false-unreach-call.i",
		"examples/svcomp/loops/lu.cmp_true-unreach-call.i",
		"examples/svcomp/loops/ludcmp_false-unreach-call.i",
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

