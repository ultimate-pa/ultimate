package de.uni_freiburg.informatik.ultimate.regressiontest.generic;

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TreeAutomizerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

public class MSODRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final long DEFAULT_TIMEOUT = 20 * 1000L;

	public MSODRegressionTestSuite() {
		super();
		mTimeout = DEFAULT_TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/smtlib/MSOD/regression");
		mFiletypesToConsider = new String[] { ".smt2" };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		final boolean unknownIsSuccess = true;
		return new TreeAutomizerTestResultDecider(runDefinition, unknownIsSuccess);
	}
}