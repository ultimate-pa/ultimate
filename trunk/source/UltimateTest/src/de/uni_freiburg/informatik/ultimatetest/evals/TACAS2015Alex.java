package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015Alex extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "TACASInterpolation2015/Kojak-FP.epf", testcases);
		//
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "TACASInterpolation2015/Kojak-TreeInterpolation.epf", testcases);
		//
		// addTestCasesFixed("ImpulseWithBE-C.xml",
		// "TACASInterpolation2015/Impulse-FP.epf", testcases);
		//
		// addTestCasesFixed("ImpulseWithBE-C.xml",
		// "TACASInterpolation2015/Impulse-TreeInterpolation.epf",
		// testcases);

		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-FP-nBE.epf", testcases);

		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", testcases);

		addTestCasesFixed("ImpulseNoBE-C.xml", "TACASInterpolation2015/Impulse-FP-nBE.epf", testcases);

		addTestCasesFixed("ImpulseNoBE-C.xml", "TACASInterpolation2015/Impulse-TreeInterpolation-nBE.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		// return -1 for all files
		return 50;
	}
	
	@Override
	protected String[] getDirectories() {
		//override if you want to use your own directories here 
		return super.getDirectories();
	}

}
