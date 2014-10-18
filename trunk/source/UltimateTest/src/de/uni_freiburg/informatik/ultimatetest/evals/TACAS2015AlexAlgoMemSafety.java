package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlexAlgoMemSafety extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		
		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-FP-mem.epf", testcases);

		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-mem.epf", testcases);

		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-FP-mem.epf", testcases);

		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-TreeInterpolation-mem.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return 50;
	}

}
