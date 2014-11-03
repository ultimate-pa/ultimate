package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class WitnessBugs extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("AutomizerC.xml", "witness/svComp-32bit-precise-Automizer-Witness.epf", testcases);
		addTestCasesFixed("CodeCheckWithBE-C.xml", "witness/svComp-32bit-precise-wit-BE-Kojak-Witness.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
				
		};
		// @formatter:on
	}

	@Override
	protected int getTimeout() {
		return 30 * 1000;
	}

}
