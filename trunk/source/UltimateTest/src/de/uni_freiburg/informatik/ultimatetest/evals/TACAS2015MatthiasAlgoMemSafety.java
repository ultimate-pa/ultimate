package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015MatthiasAlgoMemSafety extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-mem.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-IC-mem.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-LV-mem.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-IC-LV-mem.epf", testcases);
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
//			"examples/svcomp/memsafety/",
//			"examples/svcomp/memsafety-ext/",
//			"examples/svcomp/list-ext-properties/"

			//our best category
			"examples/svcomp/memory-alloca/",
		};
		return directories;
		// @formatter:on
	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}
	
	@Override
	protected String[] getFileEndings() {
		return new String[] { ".i" };
	}

}
