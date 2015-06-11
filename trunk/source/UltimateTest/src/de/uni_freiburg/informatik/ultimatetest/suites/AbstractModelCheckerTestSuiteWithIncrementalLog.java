package de.uni_freiburg.informatik.ultimatetest.suites;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.reporting.IIncrementalLog;

public abstract class AbstractModelCheckerTestSuiteWithIncrementalLog extends AbstractModelCheckerTestSuite {
	private IncrementalLogWithVMParameters mIncrementalLog;

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases.size() != 0) {
			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		return super.createTestCases();
	}
	
	protected IIncrementalLog getIncrementalLogWithVMParameters(){
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(this.getClass(), getTimeout());
		}
		return mIncrementalLog;
	}
}
