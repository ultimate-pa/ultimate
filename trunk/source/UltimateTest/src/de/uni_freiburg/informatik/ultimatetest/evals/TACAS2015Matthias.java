package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015Matthias extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		// addTestCasesFixed("AutomizerC.xml",
		// "TACASInterpolation2015/BackwardPredicates.epf", testcases);

		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/ForwardPredicates.epf", testcases);

		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/TreeInterpolation.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return 50;
	}

	@Override
	protected String[] getDirectories() {
		return new String[] { "examples/svcomp/systemc/transmitter.15_false-unreach-call_false-termination.cil.c" };
		// return super.getDirectories();
	}

}
