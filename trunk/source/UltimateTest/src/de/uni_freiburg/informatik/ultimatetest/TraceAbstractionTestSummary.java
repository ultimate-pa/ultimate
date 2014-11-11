package de.uni_freiburg.informatik.ultimatetest;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;

public class TraceAbstractionTestSummary extends NewTestSummary {

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
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category,
			String message, String testname, IResultService resultService) {
		super.addResult(ultimateRunDefinition, threeValuedResult, category, message, testname, resultService);

		if (resultService != null) {
			addTraceAbstractionBenchmarks(ultimateRunDefinition,
					de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.filterResults(resultService.getResults(), BenchmarkResult.class));
		}

	}

	public void addTraceAbstractionBenchmarks(UltimateRunDefinition ultimateRunDefinition,
			Collection<BenchmarkResult> benchmarkResults) {
		assert !m_TraceAbstractionBenchmarks.containsKey(ultimateRunDefinition) : "benchmarks already added";
		m_TraceAbstractionBenchmarks.put(ultimateRunDefinition, benchmarkResults);
	}

	@Override
	public String getSummaryLog() {

		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append("Trace Abstraction Test Summary").append(" #################")
				.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());

		PartitionedResults results = partitionResults(mResults.entrySet());

		sb.append(getSummaryLog(results.Success, "SUCCESSFUL TESTS"));
		int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(results.Unknown, "UNKNOWN TESTS"));
		int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(results.Failure, "FAILED TESTS"));
		int fail = mCount;
		total = total + mCount;
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
		sb.append("====== SUMMARY for ").append("Trace Abstraction").append(" ======")
				.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
		sb.append("Success:\t" + success).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
		sb.append("Unknown:\t" + unknown).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
		sb.append("Failures:\t" + fail).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
		sb.append("Total:\t\t" + total);
		return sb.toString();

	}

	private String getSummaryLog(Collection<Entry<UltimateRunDefinition, ExtendedResult>> results, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());

		// group by category
		HashMap<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> resultsByCategory = new HashMap<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : results) {
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> coll = resultsByCategory
					.get(entry.getValue().Category);
			if (coll == null) {
				coll = new ArrayList<>();
				resultsByCategory.put(entry.getValue().Category, coll);
			}
			coll.add(entry);
		}

		for (Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> entry : resultsByCategory
				.entrySet()) {
			sb.append("\t").append(entry.getKey()).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());

			String indent = "\t\t\t";
			for (Entry<UltimateRunDefinition, ExtendedResult> currentResult : entry.getValue()) {
				sb.append("\t\t").append(currentResult.getKey()).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
				// Add TraceAbstraction benchmarks
				Collection<BenchmarkResult> benchmarks = m_TraceAbstractionBenchmarks.get(currentResult.getKey());
				if (benchmarks == null) {
					sb.append(indent).append("No benchmark results available.").append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
				} else {
					for (BenchmarkResult<Object> benchmark : benchmarks) {
						//exclude the extensive ultimate benchmark object
						if (benchmark.getBenchmark().getClass() != Benchmark.class) {
							appendProvider(sb, indent, benchmark.getBenchmark().createCvsProvider());
						}
					}
				}
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ").append(entry.getValue().size())
					.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("\t--------").append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			mCount = mCount + entry.getValue().size();
		}
		sb.append("Count: ").append(mCount);
		sb.append("\n\n");
		return sb.toString();
	}

	private void appendProvider(StringBuilder sb, String ident, ICsvProvider<?> provider) {
		if (provider == null) {
			sb.append(ident);
			sb.append("Provider is null");
			return;
		}

		sb.append(ident);
		for (String s : provider.getColumnTitles()) {
			sb.append(s);
			sb.append(", ");
		}
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());

		if (provider.getTable() == null || provider.getTable().size() == 0) {
			sb.append(ident);
			sb.append("Provider " + provider.getClass().getSimpleName() + " has no rows");
			return;
		}

		List<String> rowHeaders = provider.getRowHeaders();
		int i = 0;
		for (List<?> row : provider.getTable()) {
			sb.append(ident);
			if (rowHeaders != null && i < rowHeaders.size()) {
				String rowHeader = rowHeaders.get(i);
				sb.append(rowHeader);
				sb.append(", ");
			}
			for (Object cell : row) {
				sb.append(cell);
				sb.append(", ");
			}
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			i++;
		}
	}

}
