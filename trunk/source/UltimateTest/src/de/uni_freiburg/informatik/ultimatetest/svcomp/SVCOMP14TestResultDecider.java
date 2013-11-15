package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.io.File;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.Util;

public class SVCOMP14TestResultDecider implements ITestResultDecider {

	/**
	 * Do not change the order of this Enum; their ordinal values are compared
	 * against each other.
	 */
	private enum ToolchainResult {
		NORESULT, CORRECT, UNPROVABLE, TIMEOUT, INCORRECT, SYNTAXERROR

	}

	private ITestSummary mSummary;
	private boolean mShouldBeSafe;
	private File mInputFile;
	private Logger mLogger;

	public SVCOMP14TestResultDecider(ITestSummary summary,
			boolean shouldbesafe, File inputFile) {
		if (summary == null) {
			throw new ExceptionInInitializerError("summary may not be null");
		}
		if (inputFile == null) {
			throw new ExceptionInInitializerError("inputFile may not be null");
		}

		mLogger = Logger.getLogger(SVCOMP14TestResultDecider.class);
		mSummary = summary;
		mShouldBeSafe = shouldbesafe;
		mInputFile = inputFile;
	}

	@Override
	public boolean isResultFail() {
		TestSummary summary = (TestSummary) mSummary;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();

		if (resultSet.isEmpty()) {
			summary.addFail(null, mInputFile.getAbsolutePath(),
					"There was no result");
			return true;
		}

		// FIXME: This is cutnpaste from result notifier ... in the long run we
		// need to find another way

		ToolchainResult toolchainResult = ToolchainResult.NORESULT;

		IResult finalResult = null;

		for (Entry<String, List<IResult>> results : resultSet) {
			List<IResult> resultList = results.getValue();
			for (IResult result : resultList) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = ToolchainResult.SYNTAXERROR;
					finalResult = result;
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult.ordinal() < ToolchainResult.UNPROVABLE
							.ordinal()) {
						toolchainResult = ToolchainResult.UNPROVABLE;
						finalResult = result;
					}
				} else if (result instanceof CounterExampleResult) {
					if (toolchainResult.ordinal() < ToolchainResult.INCORRECT
							.ordinal()) {
						toolchainResult = ToolchainResult.INCORRECT;
						finalResult = result;
					}
				} else if (result instanceof PositiveResult) {
					if (toolchainResult.ordinal() < ToolchainResult.CORRECT
							.ordinal()) {
						toolchainResult = ToolchainResult.CORRECT;
						finalResult = result;
					}
				} else if (result instanceof TimeoutResult) {
					if (toolchainResult.ordinal() < ToolchainResult.TIMEOUT
							.ordinal()) {
						toolchainResult = ToolchainResult.TIMEOUT;
						finalResult = result;
					}
				}
			}
		}

		boolean fail = true;

		String longDescription = "finalResult is null";
		if (finalResult != null) {
			longDescription = finalResult.getLongDescription();
		}

		switch (toolchainResult) {
		case SYNTAXERROR:
		case UNPROVABLE:
		case TIMEOUT:
		case NORESULT:
			summary.addUnknown(finalResult, mInputFile.getAbsolutePath(),
					longDescription);
			fail = true;
			break;
		case INCORRECT:
			if (mShouldBeSafe) {
				summary.addFail(finalResult, mInputFile.getAbsolutePath(),
						"SHOULD BE SAFE! Real message is: " + longDescription);
			} else {
				summary.addSuccess(finalResult, mInputFile.getAbsolutePath(),
						longDescription);
			}
			fail = mShouldBeSafe;
			break;
		case CORRECT:
			if (mShouldBeSafe) {
				summary.addSuccess(finalResult, mInputFile.getAbsolutePath(),
						longDescription);
			} else {
				summary.addFail(finalResult, mInputFile.getAbsolutePath(),
						"SHOULD BE UNSAFE! Real message is: " + longDescription);
			}
			fail = !mShouldBeSafe;
			break;

		default:
			throw new AssertionError("unknown result");
		}

		logResults(fail, mShouldBeSafe, toolchainResult);
		return fail;
	}

	private void logResults(boolean fail, boolean shouldbesafe,
			ToolchainResult toolchainresult) {

		Util.logResults(mLogger, mInputFile.getAbsolutePath(), fail, Arrays
				.asList("Result should be CORRECT: " + shouldbesafe,
						"Toolchain result was: " + toolchainresult));

	}

}
