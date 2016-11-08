/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.BaseTestSummary;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

public class TraceAbstractionTestSummary extends BaseTestSummary {
	
	private final boolean mShowBenchmarkResults = false; 

	private int mCount;

	/**
	 * A map from file names to benchmark results.
	 */
	private final Map<UltimateRunDefinition, Collection<ICsvProvider<?>>> mTraceAbstractionBenchmarks;

	public TraceAbstractionTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mCount = 0;
		mTraceAbstractionBenchmarks = new HashMap<UltimateRunDefinition, Collection<ICsvProvider<?>>>();
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
					ResultUtil.filterResults(resultService.getResults(), BenchmarkResult.class));
		}

	}

	@SuppressWarnings("rawtypes")
	public void addTraceAbstractionBenchmarks(UltimateRunDefinition ultimateRunDefinition,
			Collection<BenchmarkResult> benchmarkResults) {
		assert !mTraceAbstractionBenchmarks.containsKey(ultimateRunDefinition) : "benchmarks already added";

		if (benchmarkResults != null && !benchmarkResults.isEmpty()) {
			final ArrayList<ICsvProvider<?>> providers = new ArrayList<>(benchmarkResults.size());
			for (final BenchmarkResult result : benchmarkResults) {
				// exclude the extensive ultimate benchmark object
				if (result.getBenchmark().getClass() == Benchmark.class) {
					continue;
				}
				providers.add(result.getBenchmark().createCvsProvider());
			}
			if (!providers.isEmpty()) {
				mTraceAbstractionBenchmarks.put(ultimateRunDefinition, providers);
			}
		}
	}

	@Override
	public String getSummaryLog() {

		final StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append("Trace Abstraction Test Summary").append(" #################")
				.append(CoreUtil.getPlatformLineSeparator());

		final PartitionedResults results = partitionResults(mResults.entrySet());

		sb.append(getSummaryLog(results.Success, "SUCCESSFUL TESTS"));
		final int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(results.Unknown, "UNKNOWN TESTS"));
		final int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(results.Failure, "FAILED TESTS"));
		final int fail = mCount;
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
		final StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append(CoreUtil.getPlatformLineSeparator());

		// group by category
		final HashMap<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> resultsByCategory = new HashMap<>();
		for (final Entry<UltimateRunDefinition, ExtendedResult> entry : results) {
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> coll = resultsByCategory
					.get(entry.getValue().getCategory());
			if (coll == null) {
				coll = new ArrayList<>();
				resultsByCategory.put(entry.getValue().getCategory(), coll);
			}
			coll.add(entry);
		}

		for (final Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> entry : resultsByCategory
				.entrySet()) {
			sb.append("\t").append(entry.getKey()).append(CoreUtil.getPlatformLineSeparator());

			final String indent = "\t\t\t";
			for (final Entry<UltimateRunDefinition, ExtendedResult> currentResult : entry.getValue()) {
				sb.append("\t\t").append(currentResult.getKey()).append(CoreUtil.getPlatformLineSeparator());
				// Add Result Message
				sb.append(indent).append(currentResult.getValue().getMessage()).append(CoreUtil.getPlatformLineSeparator());
				if (mShowBenchmarkResults) {
					// Add TraceAbstraction benchmarks
					final Collection<ICsvProvider<?>> benchmarkProviders = mTraceAbstractionBenchmarks.get(currentResult
							.getKey());
					if (benchmarkProviders == null) {
						sb.append(indent).append("No benchmark results available.")
						.append(CoreUtil.getPlatformLineSeparator());
					} else {
						for (final ICsvProvider<?> benchmarkProvider : benchmarkProviders) {
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
		for (final String s : provider.getColumnTitles()) {
			sb.append(s);
			sb.append(", ");
		}
		sb.append(CoreUtil.getPlatformLineSeparator());

		if (provider.getTable() == null || provider.getTable().size() == 0) {
			sb.append(ident);
			sb.append("Provider " + provider.getClass().getSimpleName() + " has no rows");
			return;
		}

		final List<String> rowHeaders = provider.getRowHeaders();
		int i = 0;
		for (final List<?> row : provider.getTable()) {
			sb.append(ident);
			if (rowHeaders != null && i < rowHeaders.size()) {
				final String rowHeader = rowHeaders.get(i);
				sb.append(rowHeader);
				sb.append(", ");
			}
			for (final Object cell : row) {
				sb.append(cell);
				sb.append(", ");
			}
			sb.append(CoreUtil.getPlatformLineSeparator());
			i++;
		}
	}

}
