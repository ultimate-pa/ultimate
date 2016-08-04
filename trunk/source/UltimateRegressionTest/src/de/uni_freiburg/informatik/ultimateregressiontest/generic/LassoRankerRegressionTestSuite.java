package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.LassoRankerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;

/**
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class LassoRankerRegressionTestSuite extends AbstractRegressionTestSuite {

	public LassoRankerRegressionTestSuite() {
		super();
		mTimeout = 20 * 1000;
		mRootFolder = TestUtil.getPathFromTrunk("examples/lassos");
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new LassoRankerTestResultDecider(runDefinition.getInput()[0]);
	}


}
