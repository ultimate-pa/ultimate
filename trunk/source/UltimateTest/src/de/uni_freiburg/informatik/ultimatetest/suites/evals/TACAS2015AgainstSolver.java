package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AgainstSolver extends TACAS2015 {

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/ForwardPredicates.epf", getPairs());
		addTestCases("AutomizerC.xml", "TACASInterpolation2015/TreeInterpolation.epf", getPairs());
		addTestCases("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-FP-nBE.epf", getPairs());
		addTestCases("CodeCheckNoBE-C.xml", "TACASInterpolation2015/Kojak-TreeInterpolation-nBE.epf", getPairs());
		return super.createTestCases();
	}
}
