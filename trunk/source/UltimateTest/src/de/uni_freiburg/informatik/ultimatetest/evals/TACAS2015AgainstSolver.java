package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AgainstSolver extends TACAS2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/ForwardPredicates.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/TreeInterpolation.epf", testcases);
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-FP-nBE.epf", testcases);
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", testcases);		
	}
}
