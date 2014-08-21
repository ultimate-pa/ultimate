package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TraceAbstractionTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class TraceAbstractionTestSummary extends TestSummary {

	private int mCount;

	private String mLogFilePath;
	/**
	 * A map from file names to benchmark results.
	 */
	private Map<String, Collection<BenchmarkResult>> m_TraceAbstractionBenchmarks;

	public TraceAbstractionTestSummary(String testSuiteCanonicalName, String description) {
		super(testSuiteCanonicalName);
		mLogFilePath = Util.generateSummaryLogFilename(
				Util.getPathFromSurefire(".", this.getClass().getCanonicalName()), description);
		mCount = 0;
		m_TraceAbstractionBenchmarks = new HashMap<String, Collection<BenchmarkResult>>();
	}

	@Override
	public void addResult(TestResult actualResult, boolean junitResult, String category, UltimateRunDefinition ultimateRunDefinition, String message) {
		super.addResult(actualResult, junitResult, category, ultimateRunDefinition, message);

		ITestResultDecider decider = getTestResultDecider();
		if (decider instanceof TraceAbstractionTestResultDecider) {
			addTraceAbstractionBenchmarks(ultimateRunDefinition.getInput().getAbsolutePath(), Util.filterResults(
					((TraceAbstractionTestResultDecider) decider).getUltimateResults(), BenchmarkResult.class));
		}

	}

	public void addTraceAbstractionBenchmarks(String filename, Collection<BenchmarkResult> benchmarkResults) {
		assert !m_TraceAbstractionBenchmarks.containsKey(filename) : "benchmarks already added";
		m_TraceAbstractionBenchmarks.put(filename, benchmarkResults);
	}

	@Override
	public String getSummaryLog() {

		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append("Trace Abstraction Test Summary").append(" #################")
				.append("\n");

		sb.append(getSummaryLog(getSummaryMap(TestResult.SUCCESS), "SUCCESSFUL TESTS"));
		int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(getSummaryMap(TestResult.UNKNOWN), "UNKNOWN TESTS"));
		int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(getSummaryMap(TestResult.FAIL), "FAILED TESTS"));
		int fail = mCount;
		total = total + mCount;
		sb.append("\n");
		sb.append("====== SUMMARY for ").append("Trace Abstraction").append(" ======").append("\n");
		sb.append("Success:\t" + success).append("\n");
		sb.append("Unknown:\t" + unknown).append("\n");
		sb.append("Failures:\t" + fail).append("\n");
		sb.append("Total:\t\t" + total);
		return sb.toString();

	}

	private String getSummaryLog(Map<String, Summary> map, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append("\n");
		for (Entry<String, Summary> entry : map.entrySet()) {
			sb.append("\t").append(entry.getKey()).append("\n");

			for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
				sb.append("\t\t").append(fileMsgPair.getKey()).append(": ").append(fileMsgPair.getValue()).append("\n");
				// Add TraceAbstraction benchmarks
				Collection<BenchmarkResult> benchmarks = m_TraceAbstractionBenchmarks.get(fileMsgPair.getKey());
				if (benchmarks == null) {
					sb.append("\t\t").append("No benchmark results available.").append("\n");
				} else {
					for (BenchmarkResult benchmark : benchmarks) {
						sb.append("\t\t").append(benchmark.getLongDescription()).append("\n");
					}
				}
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ").append(entry.getValue().getCount())
					.append("\n");
			sb.append("\t--------").append("\n");
			mCount = mCount + entry.getValue().getCount();
		}
		sb.append("Count: ").append(mCount);
		sb.append("\n\n");
		return sb.toString();
	}

	@Override
	public File getSummaryLogFileName() {
		return new File(mLogFilePath);
	}
}
