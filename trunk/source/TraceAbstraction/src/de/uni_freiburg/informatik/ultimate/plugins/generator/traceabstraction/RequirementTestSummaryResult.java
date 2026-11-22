package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * Summarizes the outcome of all TestScenarios of a requirements file.
 *
 * The long description lists every TestScenario, one per line starting with "  - TestScenario &lt;id&gt; ", below the
 * headings "Passed (n):", "Failed (n):" and "Not analyzed (n):". Details of a failed TestScenario follow on more deeply
 * indented lines.
 */
public class RequirementTestSummaryResult implements IResult {

	private final String mPlugin;
	private final List<String> mPassed;
	private final List<String> mFailed;
	private final List<String> mNotAnalyzed;

	public RequirementTestSummaryResult(final String plugin, final List<String> passed, final List<String> failed,
			final List<String> notAnalyzed) {
		mPlugin = plugin;
		mPassed = passed;
		mFailed = failed;
		mNotAnalyzed = notAnalyzed;
	}

	@Override
	public String getShortDescription() {
		return "Test scenarios: " + mPassed.size() + "/" + getTotal() + " passed";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("\nTest Scenario Summary\n");
		sb.append("---------------------\n");
		sb.append("Passed: ").append(mPassed.size()).append('/').append(getTotal()).append('\n');
		appendList(sb, "Passed", mPassed);
		appendList(sb, "Failed", mFailed);
		appendList(sb, "Not analyzed", mNotAnalyzed);
		return sb.toString();
	}

	private int getTotal() {
		return mPassed.size() + mFailed.size() + mNotAnalyzed.size();
	}

	private static void appendList(final StringBuilder sb, final String heading, final List<String> messages) {
		if (messages.isEmpty()) {
			return;
		}
		sb.append(heading).append(" (").append(messages.size()).append("):\n");
		for (final String message : messages) {
			sb.append("  - ").append(message).append('\n');
		}
	}

	@Override
	public String getPlugin() {
		return mPlugin;
	}
}
