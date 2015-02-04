package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlgoComparison extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-IC.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-LV.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/SP-IC-LV.epf", testcases);	
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP.epf", testcases);
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-IC.epf", testcases);
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-LV.epf", testcases);
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-SP-IC-LV.epf", testcases);
	}	
	
	@Override
	protected int getTimeout() {
		return 30 * 1000;
	}
}
