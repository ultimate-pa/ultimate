package de.uni_freiburg.informatik.ultimate.test.reporting;

import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ExtendedResult {
	private final TestResult mResult;
	private final String mMessage;
	private final String mCategory;
	private final String mTestname;

	public ExtendedResult(final TestResult result, final String message, final String category, final String testname) {
		mResult = result;
		mMessage = message;
		mCategory = category;
		mTestname = testname;
	}

	public TestResult getResult() {
		return mResult;
	}

	public String getMessage() {
		return mMessage;
	}

	public String getCategory() {
		return mCategory;
	}

	public String getTestname() {
		return mTestname;
	}
}
