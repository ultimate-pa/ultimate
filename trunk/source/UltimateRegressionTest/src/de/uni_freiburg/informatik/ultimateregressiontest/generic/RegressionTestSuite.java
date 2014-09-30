package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider2;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * @author dietsch
 * 
 */
public class RegressionTestSuite extends AbstractRegressionTestSuite {

	public RegressionTestSuite() {
		super();
		mTimeout = 5000;
		mRootFolder = Util.getPathFromTrunk("examples/");

		// match every path not containing CToBoogieTranslation
		mFilterRegex = "((?!CToBoogieTranslation)[\\s\\S])*";
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		// does not use any summary
		return new ITestSummary[0];
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new SafetyCheckTestResultDecider2(runDefinition, false);
	}

}
