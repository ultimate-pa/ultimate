package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlgoComparisonArray extends TACAS2015 {

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_Interpolation.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Princess_Interpolation.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_Interpolation.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC-LV.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC-LV.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/CVC4_SP-IC-LV.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/CVC4_SP-IC.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-LV.epf", getPairs());

		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-IC.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-LV.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-IC-LV.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SMTInterpol.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-Princess.epf", getPairs());
		return super.createTestCases();
	}

	@Override
	protected long getTimeout() {
		return 60 * 1000;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
		    "examples/svcomp/heap-manipulation",
		    "examples/svcomp/list-properties",
		    "examples/svcomp/ldv-regression",
		    
		    "examples/svcomp/loops",
		    "examples/svcomp/loop-acceleration",
		    "examples/svcomp/loop-invgen",
		    "examples/svcomp/loop-lit",
		    "examples/svcomp/loop-new",

		};
		return directories;
		// @formatter:on
	}

	@Override
	protected String[] getFileEndings() {
		return new String[] { ".i" };
	}
}
