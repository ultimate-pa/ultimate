package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.BacktranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class BoogieBacktranslationRegressionTestSuite extends AbstractRegressionTestSuite {

	private static String sRootFolder = Util.getPathFromTrunk("examples/Backtranslation");
	private static String sFileending = ".bpl";

	public BoogieBacktranslationRegressionTestSuite() {
		super();
		mTimeout = 500000;
		mRootFolder = sRootFolder;
		mFiletypesToConsider = new String[] { sFileending };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new BacktranslationTestResultDecider(runDefinition.getInput().getAbsolutePath(), sFileending);
	}
}
