package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlgoComparisonArray extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {

		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/Princess_Interpolation.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_Interpolation.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC-LV.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC-LV.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-LV.epf", testcases);

//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP.epf", testcases);
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-IC.epf", testcases);
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-LV.epf", testcases);
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-IC-LV.epf", testcases);
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SMTInterpol.epf", testcases);
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-Princess.epf", testcases);
	}

	@Override
	protected int getTimeout() {
		return 60 * 1000;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
		    "examples/svcomp/heap-manipulation",
		    "examples/svcomp/list-properties",
		    "examples/svcomp/ldv-regression",
		    "examples/svcomp/loops",
		};
		return directories;
		// @formatter:on
	}

	@Override
	protected String[] getFileEndings() {
		return new String[] { ".i" };
	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}
}
