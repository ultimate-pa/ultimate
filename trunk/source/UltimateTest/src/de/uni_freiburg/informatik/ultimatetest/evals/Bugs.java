package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class Bugs extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {

		// addTestCasesFixed("AutomizerC.xml",
		// "TACASInterpolation2015/ForwardPredicates.epf", testcases);
		//
		addTestCasesFixed("AutomizerC.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf", testcases);

		// addTestCasesFixed("AutomizerC.xml",
		// "svcomp2015/svComp-32bit-precise.epf", testcases);
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "svcomp2015/svComp-32bit-precise-BE-Kojak.epf", testcases);
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "svcomp2015/svComp-32bit-memsafety-BE-Kojak.epf.epf", testcases);
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf.epf", testcases);

		// addTestCasesFixed("AutomizerC.xml",
		// "TACASInterpolation2015/TreeInterpolation.epf", testcases);

		// addTestCasesFixed("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-FP-nBE.epf", testcases);
		//
		// addTestCasesFixed("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", testcases);
		//
		// addTestCasesFixed("ImpulseNoBE-C.xml",
		// "TACASInterpolation2015/Impulse-FP-nBE.epf", testcases);
		//
		// addTestCasesFixed("ImpulseNoBE-C.xml",
		// "TACASInterpolation2015/Impulse-TreeInterpolation-nBE.epf",
		// testcases);
		//
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "TACASInterpolation2015/Kojak-FP.epf", testcases);
		//
		// addTestCasesFixed("CodeCheckWithBE-C.xml",
		// "TACASInterpolation2015/Kojak-TreeInterpolation.epf", testcases);
		//
		// addTestCasesFixed("ImpulseWithBE-C.xml",
		// "TACASInterpolation2015/Impulse-FP.epf", testcases);
		//
		// addTestCasesFixed("ImpulseWithBE-C.xml",
		// "TACASInterpolation2015/Impulse-TreeInterpolation.epf", testcases);
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
//			"examples/svcomp/ssh/s3_srvr.blast.16_false-unreach-call.i.cil.c",
//			"examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-termination.cil.c",
//			"examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i",
			
				//nutz, backtranslation, works
//				"examples/svcomp/ssh/s3_srvr.blast.16_false-unreach-call.i.cil.c",
				//matthias, preprocessor

				//need to change bpl from recursive to iterative
//				"examples/svcomp/array-examples/data_structures_set_multi_proc_false-unreach-call_ground.i",
 
//			"examples/svcomp/array-examples/data_structures_set_multi_proc_trivial_true-unreach-call_ground.i",

//			"examples/svcomp/array-examples/data_structures_set_multi_proc_true-unreach-call_ground.i"
				
		};
		// @formatter:on
		// return super.getDirectories();
	}

	@Override
	protected int getTimeout() {
		return 600 * 1000;
	}

}
