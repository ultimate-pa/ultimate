package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.BoogieBacktranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class BoogieBacktranslationRegressionTestSuite extends AbstractRegressionTestSuite {

	private static String sRootFolder = Util.getPathFromTrunk("examples/BoogiePL/Backtranslation");

	public BoogieBacktranslationRegressionTestSuite() {
		super();
		mTimeout = 5000;
		mRootFolder = sRootFolder;
		mFiletypesToConsider = new String[] { ".bpl" };
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		// does not use any summary
		return new ITestSummary[0];
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new BoogieBacktranslationTestResultDecider(runDefinition.getInput().getAbsolutePath());
	}
}
