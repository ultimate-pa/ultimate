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
	private static final String[] s_SVCOMP_Reach_PreciseMemoryModel = {
		// Failed tests from before fix of "old(vars) only assigned on first call".
		// Sorted by line count in ascending order
//		"examples/svcomp/list-properties/simple_true-unreach-call.i",
//		"examples/svcomp/list-properties/list_flag_true-unreach-call.i",
//		"examples/svcomp/list-properties/alternating_list_true-unreach-call.i",
//		"examples/svcomp/list-properties/splice_true-unreach-call.i",
//		"examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call.i",
//		"examples/svcomp/heap-manipulation/merge_sort_true-unreach-call.i",
//		"examples/svcomp/list-properties/list_search_true-unreach-call.i",
//		"examples/svcomp/heap-manipulation/bubble_sort_linux_true-unreach-call.i",

		// Failed tests from after fix of "old(vars) only assigned on first call".
		// These tests fail, even without inlining
		"examples/svcomp/loop-acceleration/diamond_true-unreach-call2.c",
		"examples/svcomp/loop-lit/afnp2014_true-unreach-call.c",
		"examples/svcomp/loop-lit/bhmr2007_true-unreach-call.c.i",
		"exampltruees/svcomp/loop-lit/cggmp2005_true-unreach-call.c",
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

	/** Files to be tested. */
	private static final String[] s_SVCOMP_Memsafety = {
		// These test fail with and without inlining
//		"examples/svcomp/list-ext-properties/test-0158_1_true-valid-memsafety.i",
//		"examples/svcomp/list-ext-properties/test-0214_1_true-valid-memsafety.i",
//		"examples/svcomp/list-ext-properties/test-0217_1_true-valid-memsafety.i",
		
		// These tests failed only with inlining. But now they pass, although I didn't changed anything
//		"examples/svcomp/list-ext-properties/test-0019_1_false-valid-memtrack.i",
//		"examples/svcomp/memory-alloca/bubblesort-alloca_true-valid-memsafety.i",
//		"examples/svcomp/memory-alloca/cstrcat-alloca_true-valid-memsafety.i",
//		"examples/svcomp/memory-alloca/cstrncat-alloca_true-valid-memsafety.i",

		// These tests fail only with inlining.
		"examples/svcomp/list-ext-properties/test-0158_1_false-valid-memtrack.i", // fail
	};
	
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}
	
	private static final boolean sReachPreciseMemoryModel = false;
	private static final boolean sMemsafety = true;

	private static final boolean sAutomizerWithInlining = true;
	private static final boolean sAutomizerWithoutInlining = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (sReachPreciseMemoryModel) {
			for (String file : s_SVCOMP_Reach_PreciseMemoryModel) {
				if (sAutomizerWithInlining) {
					addTestCase("AutomizerCInline.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf", file);
				}
				if (sAutomizerWithoutInlining) {
					addTestCase("AutomizerC.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf",  file);
				}
			}
		}
		if (sMemsafety) {
			for (String file : s_SVCOMP_Memsafety) {
				if (sAutomizerWithInlining) {
					addTestCase("AutomizerCInline.xml", "automizer/ForwardPredicates_SvcompMemsafety.epf", file);
				}
				if (sAutomizerWithoutInlining) {
					addTestCase("AutomizerC.xml", "automizer/ForwardPredicates_SvcompMemsafety.epf",  file);
				}
			}
		}
		return super.createTestCases();
	}

}

