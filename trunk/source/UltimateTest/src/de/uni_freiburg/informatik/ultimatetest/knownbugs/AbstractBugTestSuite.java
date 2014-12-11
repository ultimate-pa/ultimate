package de.uni_freiburg.informatik.ultimatetest.knownbugs;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summary.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TestSummaryWithBenchmarkResults;

public abstract class AbstractBugTestSuite extends AbstractModelCheckerTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	protected int getTimeout() {
		return 300 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases.size() == 0) {
			fillTestCases();
			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		return super.createTestCases();
	}

	protected abstract void fillTestCases();

	protected void addTestCase(String toolchain, String settings, String input) {
		addTestCase(toolchain, settings, input, getTimeout());
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new TraceAbstractionTestSummary(getClass()), };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(getClass(), getTimeout());
		}
		return new IIncrementalLog[] { mIncrementalLog, new TestSummaryWithBenchmarkResults(getClass()) };
	}

}
