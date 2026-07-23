package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * Summarizes the outcome of all TestCasePositivePattern/TestCaseNegativePattern requirements in a requirements file:
 * how many of the fixed example traces behaved as expected against the translated requirement automata.
 */
public class RequirementTestSummaryResult implements IResult {

	private final int mPassed;
	private final int mTotal;
	private final List<String> mFailed;
	private final String mPlugin;

	public RequirementTestSummaryResult(final String plugin, final int passed, final int total,
			final List<String> failed) {
		mPlugin = plugin;
		mPassed = passed;
		mTotal = total;
		mFailed = failed;
	}

	@Override
	public String getShortDescription() {
		return "Test cases: " + mPassed + "/" + mTotal + " passed";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("\nTest Case Summary\n");
		sb.append("-----------------\n");
		sb.append("Passed: ").append(mPassed).append('/').append(mTotal).append('\n');

		if (!mFailed.isEmpty()) {
			sb.append("Failed (").append(mFailed.size()).append("):\n");
			for (final String message : mFailed) {
				sb.append("  - ").append(message).append('\n');
			}
		}

		return sb.toString();
	}

	@Override
	public String getPlugin() {
		return mPlugin;
	}
}