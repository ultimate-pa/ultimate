package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlexBE extends TACASInterpolation2015 {

	@Override
	protected void createTestCasesForReal(List<UltimateTestCase> testcases) {
		 addTestCasesFixed("CodeCheckWithBE-C.xml",
		 "TACASInterpolation2015/Kojak-FP.epf", testcases);
		
		 addTestCasesFixed("CodeCheckWithBE-C.xml",
		 "TACASInterpolation2015/Kojak-TreeInterpolation.epf", testcases);
		
		 addTestCasesFixed("ImpulseWithBE-C.xml",
		 "TACASInterpolation2015/Impulse-FP.epf", testcases);
		
		 addTestCasesFixed("ImpulseWithBE-C.xml",
		 "TACASInterpolation2015/Impulse-TreeInterpolation.epf",
		 testcases);
	}

	@Override
	protected int getFilesPerCategory() {
		// return -1 for all files
		return 25;
	}
	
	@Override
	protected String[] getDirectories() {
		//override if you want to use your own directories here 
		return super.getDirectories();
	}

}
