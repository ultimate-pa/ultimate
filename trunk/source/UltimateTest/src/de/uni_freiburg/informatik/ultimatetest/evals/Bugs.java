package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class Bugs extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		addTestCasesFixed("CodeCheckWithBE-C.xml", "svcomp2015/svComp-32bit-precise-BE-Impulse.epf", testcases);
		addTestCasesFixed("AutomizerC.xml", "svcomp2015/svComp-32bit-precise-Automizer.epf", testcases);

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
				"examples/svcomp/bitvector-regression/integerpromotion_true-unreach-call.i",
				"examples/svcomp/bitvector/num_conversion_2_true-unreach-call.i",
				"examples/svcomp/bitvector/soft_float_4_true-unreach-call.c.cil.c",
				"examples/svcomp/bitvector/soft_float_1_true-unreach-call.c.cil.c",
				"examples/svcomp/bitvector/parity_true-unreach-call.i",
				"examples/svcomp/bitvector-regression/signextension_true-unreach-call.i",
				"examples/svcomp/bitvector-regression/signextension_false-unreach-call.i",
				"examples/svcomp/bitvector-regression/pointer_extension2_false-unreach-call.i",
				"examples/svcomp/loop-invgen/SpamAssassin-loop_false-unreach-call.i",
				"examples/svcomp/loop-invgen/NetBSD_loop_false-unreach-call.i",
				"examples/svcomp/array-examples/standard_allDiff2_false-unreach-call_ground.i",
				"examples/svcomp/ssh-simplified/s3_srvr_11_false-unreach-call.cil.c",
				
		};
		// @formatter:on
	}

	@Override
	protected int getTimeout() {
		return 30 * 1000;
	}

}
