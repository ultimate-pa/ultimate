package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class SoundnessBugs extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {

		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/ForwardPredicates.epf", testcases);

		addTestCasesFixed("AutomizerC.xml", "TACASInterpolation2015/TreeInterpolation.epf", testcases);

//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-FP-nBE.epf", testcases);
//
//		addTestCasesFixed("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", testcases);
//
//		addTestCasesFixed("ImpulseNoBE-C.xml", "TACASInterpolation2015/Impulse-FP-nBE.epf", testcases);
//
//		addTestCasesFixed("ImpulseNoBE-C.xml", "TACASInterpolation2015/Impulse-TreeInterpolation-nBE.epf", testcases);
//
//		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-FP.epf", testcases);
//
//		addTestCasesFixed("CodeCheckWithBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation.epf", testcases);
//
//		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-FP.epf", testcases);
//
//		addTestCasesFixed("ImpulseWithBE-C.xml", "TACASInterpolation2015/Impulse-TreeInterpolation.epf", testcases);
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
			"examples/svcomp/eca-rers2012/Problem01_label15_false-unreach-call.c",
			"examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-termination.cil.c",
			"examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-termination.cil.c",
			"examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-termination.cil.c",
			"examples/svcomp/recursive/BallRajamani-SPIN2000-Fig1_false-unreach-call.c",
			"examples/svcomp/systemc/kundu1_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/kundu2_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/pipeline_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/token_ring.01_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/token_ring.02_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/token_ring.03_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/token_ring.04_false-unreach-call_false-termination.cil.c",
			"examples/svcomp/systemc/token_ring.05_false-unreach-call_false-termination.cil.c" 
		};
		// @formatter:on
		// return super.getDirectories();
	}

}
