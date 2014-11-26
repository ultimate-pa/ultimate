package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class LTLChecker extends AbstractEvaluationTestSuite {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {

		addTestCasesFixed("LtlSoftwareModelCheckingC.xml", "LtlSoftwareModelCheckingC.epf", testcases);

	}

	@Override
	protected int getFilesPerCategory() {
		return 50;
	}

	@Override
	protected String[] getDirectories() {
		return new String[] { 
				"examples/LTL/simple/",
		};
//		 return super.getDirectories();
	}

}
