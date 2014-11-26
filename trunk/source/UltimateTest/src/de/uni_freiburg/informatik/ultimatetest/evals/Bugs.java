package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class Bugs extends AbstractEvaluationTestSuite {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", testcases);
//		addTestCasesFixed("AutomizerC.xml", "svcomp2015/svComp-32bit-precise-Automizer.epf", testcases);

	}

	@Override
	protected int getFilesPerCategory() {
		// return -1 for all files
		return -1;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
				"examples/svcomp/recursive/Fibonacci04_false-unreach-call_true-termination.c",
				"examples/svcomp/recursive/MultCommutative_true-unreach-call_true-termination.c",
				"examples/svcomp/systemc/pipeline_true-unreach-call_false-termination.cil.c",
				"examples/svcomp/systemc/transmitter.03_false-unreach-call_false-termination.cil.c",
				"examples/svcomp/systemc/transmitter.04_false-unreach-call_false-termination.cil.c",
				"examples/svcomp/systemc/transmitter.06_false-unreach-call_false-termination.cil.c",
				
		};
		// @formatter:on
	}

	@Override
	protected int getTimeout() {
		return 120 * 1000;
	}

}
