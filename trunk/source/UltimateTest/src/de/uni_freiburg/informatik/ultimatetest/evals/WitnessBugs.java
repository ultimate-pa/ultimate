package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class WitnessBugs extends AbstractEvaluationTestSuite {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("AutomizerC.xml", "witness/svComp-32bit-precise-Automizer-Witness.epf", testcases);
		addTestCasesFixed("CodeCheckWithBE-C.xml", "witness/svComp-32bit-precise-BE-Impulse-Witness.epf", testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		return -1;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		return new String[] { 
			//difference between codecheck and automizer 
			"examples/svcomp/ssh-simplified/s3_srvr_10_false-unreach-call.cil.c",
//			"examples/Backtranslation/regression/c/standard/Loops.c",
			
			
			"examples/svcomp/systemc/kundu1_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i",
			
			// works 
			 "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-termination.cil.c"
		};
		// @formatter:on
	}

	@Override
	protected int getTimeout() {
		return 120 * 1000;
	}
}
