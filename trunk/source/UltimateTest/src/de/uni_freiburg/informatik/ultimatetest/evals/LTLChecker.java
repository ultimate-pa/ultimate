package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.LTLCheckerTestResultDecider;

public class LTLChecker extends AbstractEvaluationTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new LTLCheckerTestResultDecider(urd, false);
	}
	
	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("LtlSoftwareModelCheckingC.xml", "LtlSoftwareModelCheckingC.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return 20;
	}

	@Override
	protected String[] getDirectories() {
		return new String[] { 
				"examples/LTL/rers/",
		};
//		 return super.getDirectories();
	}
	
	@Override
	protected int getTimeout() {
		return 20 * 60 * 1000;
	}

}
