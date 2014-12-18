package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015MatthiasAlgoMemSafety extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {

//		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer-FP-mem.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "automizer/ForwardPredicates.epf", testcases);
//		"automizer/ForwardPredicates.epf"
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
				// not good for CodeCheck
//			"examples/svcomp/eca-rers2012/",
//				"examples/svcomp/loop-invgen/",
//				"examples/svcomp/loop-new/",				
				
//			"examples/svcomp/ntdrivers-simplified/",
//   		"examples/svcomp/ssh-simplified/", 
//			"examples/svcomp/locks/",
//			"examples/svcomp/recursive/", 
//			"examples/svcomp/systemc/",
//				"examples/svcomp/heap-manipulation/"
				"examples/svcomp/memsafety/"
//				"examples/svcomp/ntdrivers/"
		};
		return directories;
		// @formatter:on
	}

	@Override
	protected int getFilesPerCategory() {
		return 50;
	}

}
