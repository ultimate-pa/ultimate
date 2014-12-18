package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlexAlgoMemSafety extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		
		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-FP-mem.epf", testcases);

		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-mem.epf", testcases);

		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-FP-mem.epf", testcases);

		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-TreeInterpolation-mem.epf", testcases);
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
		};
		return directories;
		// @formatter:on
	}

	@Override
	protected int getFilesPerCategory() {
		return 50;
	}

}
