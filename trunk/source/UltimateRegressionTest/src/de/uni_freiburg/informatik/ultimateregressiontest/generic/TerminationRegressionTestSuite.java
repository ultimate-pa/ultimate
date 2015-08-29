package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TerminationAnalysisTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class TerminationRegressionTestSuite extends AbstractRegressionTestSuite {

	public TerminationRegressionTestSuite() {
		super();
		mTimeout = 20 * 1000;
		mRootFolder = TestUtil.getPathFromTrunk("examples/");

		mFilterRegex = ".*(lassos|termination).*";
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new TerminationAnalysisTestResultDecider(runDefinition, false);
	}


}
