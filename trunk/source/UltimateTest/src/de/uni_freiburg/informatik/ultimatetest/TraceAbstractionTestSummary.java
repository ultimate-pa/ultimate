package de.uni_freiburg.informatik.ultimatetest;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.OldTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class TraceAbstractionTestSummary extends OldTestSummary {

	private int mCount;

	/**
	 * A map from file names to benchmark results.
	 */
	private Map<UltimateRunDefinition, Collection<BenchmarkResult>> m_TraceAbstractionBenchmarks;

	public TraceAbstractionTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mCount = 0;
		m_TraceAbstractionBenchmarks = new HashMap<UltimateRunDefinition, Collection<BenchmarkResult>>();
	}
	
	@Override
	public String getFilenameExtension() {
		return ".log";
	}
	
	@Override
	public String getDescriptiveLogName() {
		return this.getClass().getSimpleName();
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category, String message, String testname, IResultService resultService) {
		super.addResult(ultimateRunDefinition, threeValuedResult, category, message, testname, resultService);

			addTraceAbstractionBenchmarks(ultimateRunDefinition, Util.filterResults(
					resultService.getResults(), BenchmarkResult.class));

	}

	public void addTraceAbstractionBenchmarks(UltimateRunDefinition ultimateRunDefinition, Collection<BenchmarkResult> benchmarkResults) {
		assert !m_TraceAbstractionBenchmarks.containsKey(ultimateRunDefinition) : "benchmarks already added";
		m_TraceAbstractionBenchmarks.put(ultimateRunDefinition, benchmarkResults);
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
					for (BenchmarkResult<Object> benchmark : benchmarks) {
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

}
