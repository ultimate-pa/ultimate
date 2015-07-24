package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.reporting.NewTestSummary;

public class TraceAbstractionTestSummary extends NewTestSummary {
	
	private final boolean mShowBenchmarkResults = false; 

	private int mCount;

	/**
	 * A map from file names to benchmark results.
	 */
	private Map<UltimateRunDefinition, Collection<ICsvProvider<?>>> m_TraceAbstractionBenchmarks;

	public TraceAbstractionTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mCount = 0;
		m_TraceAbstractionBenchmarks = new HashMap<UltimateRunDefinition, Collection<ICsvProvider<?>>>();
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
					CoreUtil.filterResults(resultService.getResults(), BenchmarkResult.class));
		}

	}

	@SuppressWarnings("rawtypes")
	public void addTraceAbstractionBenchmarks(UltimateRunDefinition ultimateRunDefinition,
			Collection<BenchmarkResult> benchmarkResults) {
		assert !m_TraceAbstractionBenchmarks.containsKey(ultimateRunDefinition) : "benchmarks already added";

		if (benchmarkResults != null && !benchmarkResults.isEmpty()) {
			ArrayList<ICsvProvider<?>> providers = new ArrayList<>(benchmarkResults.size());
			for (BenchmarkResult result : benchmarkResults) {
				// exclude the extensive ultimate benchmark object
				if (result.getBenchmark().getClass() == Benchmark.class) {
					continue;
				}
				providers.add(result.getBenchmark().createCvsProvider());
			}
			if (!providers.isEmpty()) {
				m_TraceAbstractionBenchmarks.put(ultimateRunDefinition, providers);
			}
		}
	}

	@Override
	public String getSummaryLog() {

		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append("Trace Abstraction Test Summary").append(" #################")
				.append(CoreUtil.getPlatformLineSeparator());

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
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("====== SUMMARY for ").append("Trace Abstraction").append(" ======")
				.append(CoreUtil.getPlatformLineSeparator());
		sb.append("Success:\t" + success).append(CoreUtil.getPlatformLineSeparator());
		sb.append("Unknown:\t" + unknown).append(CoreUtil.getPlatformLineSeparator());
		sb.append("Failures:\t" + fail).append(CoreUtil.getPlatformLineSeparator());
		sb.append("Total:\t\t" + total);
		return sb.toString();

	}

	private String getSummaryLog(Collection<Entry<UltimateRunDefinition, ExtendedResult>> results, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append(CoreUtil.getPlatformLineSeparator());

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
			sb.append("\t").append(entry.getKey()).append(CoreUtil.getPlatformLineSeparator());

			String indent = "\t\t\t";
			for (Entry<UltimateRunDefinition, ExtendedResult> currentResult : entry.getValue()) {
				sb.append("\t\t").append(currentResult.getKey()).append(CoreUtil.getPlatformLineSeparator());
				// Add Result Message
				sb.append(indent).append(currentResult.getValue().Message).append(CoreUtil.getPlatformLineSeparator());
				if (mShowBenchmarkResults) {
					// Add TraceAbstraction benchmarks
					Collection<ICsvProvider<?>> benchmarkProviders = m_TraceAbstractionBenchmarks.get(currentResult
							.getKey());
					if (benchmarkProviders == null) {
						sb.append(indent).append("No benchmark results available.")
						.append(CoreUtil.getPlatformLineSeparator());
					} else {
						for (ICsvProvider<?> benchmarkProvider : benchmarkProviders) {
							appendProvider(sb, indent, benchmarkProvider);
						}
					}
				}
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ").append(entry.getValue().size())
					.append(CoreUtil.getPlatformLineSeparator());
			sb.append("\t--------").append(CoreUtil.getPlatformLineSeparator());
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
		sb.append(CoreUtil.getPlatformLineSeparator());

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
			sb.append(CoreUtil.getPlatformLineSeparator());
			i++;
		}
	}

}
