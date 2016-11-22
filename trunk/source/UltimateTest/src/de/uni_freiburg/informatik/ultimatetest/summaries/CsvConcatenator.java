/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderTransformerCombinator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderTransformer;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Summarizes all benchmarks of a certain class to a CSV. Searches through all
 * {@link de.uni_freiburg.informatik.ultimate.core.model.results.IResult result}s and takes only the
 * {@link de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult benchmark result}s whose benchmark is an
 * {@link ICsvProvider} of a specified type. Each row is extended by an entry for the following.
 * <ul>
 * <li>File</li>
 * <li>Setting</li>
 * <li>Toolchain</li>
 * </ul>
 * Furthermore the rows of each Benchmark and each test case are concatenated to a single CSV.
 *
 *
 * DD 2016-10-21: This class and some of its referenced classes re-implement various aspects of {@link ColumnDefinition}
 * , {@link ColumnDefinitionUtil} and {@link BaseCsvProviderSummary}. Why? It would have been nicer to combine the
 * functionality.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class CsvConcatenator implements ITestSummary {
	private final Class<? extends UltimateTestSuite> mUltimateTestSuite;
	private final Class<? extends ICsvProviderProvider<?>> mBenchmark;
	private final ICsvProviderTransformer<Object> mTransformer;
	private ICsvProvider<Object> mCsvProvider;

	/**
	 * Constructor with a transformer which is automatically applied to the result in {@link #getSummaryLog()}.
	 *
	 * @param ultimateTestSuite
	 *            Ultimate test suite
	 * @param benchmark
	 *            benchmark
	 * @param transformer
	 *            transformer which is applied before output
	 */
	public CsvConcatenator(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Class<? extends ICsvProviderProvider<?>> benchmark,
			final ICsvProviderTransformer<Object> transformer) {
		this(ultimateTestSuite, benchmark, Collections.singletonList(transformer));
	}

	public CsvConcatenator(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Class<? extends ICsvProviderProvider<?>> benchmark) {
		this(ultimateTestSuite, benchmark, Collections.emptyList());
	}

	public CsvConcatenator(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Class<? extends ICsvProviderProvider<?>> benchmark,
			final List<ICsvProviderTransformer<Object>> transformers) {
		mUltimateTestSuite = ultimateTestSuite;
		mBenchmark = benchmark;
		mTransformer = new CsvProviderTransformerCombinator<>(transformers);
		final List<String> emtpyList = Collections.emptyList();
		mCsvProvider = new SimpleCsvProvider<>(emtpyList);
	}

	@Override
	public String getSummaryLog() {
		final ICsvProvider<Object> csvProvider =
				(mTransformer == null) ? mCsvProvider : mTransformer.transform(mCsvProvider);
		return csvProvider.toCsv(null, null).toString();
	}

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return mUltimateTestSuite;
	}

	@Override
	public String getDescriptiveLogName() {
		return "Csv" + mBenchmark.getSimpleName() + getTransformerId();
	}

	private String getTransformerId() {
		// to be able to distinguish two CsvConcatenator instances with different transformers, we have to create a hash
		// over the transformers here
		return String.valueOf(mTransformer.hashCode());
	}

	@Override
	public String getFilenameExtension() {
		return ".csv";
	}

	@SuppressWarnings("unchecked")
	@Override
	public void addResult(final UltimateRunDefinition ultimateRunDefinition, final TestResult threeValuedResult,
			final String category, final String message, final String testname, final IResultService resultService) {
		if (resultService == null) {
			return;
		}
		for (final ICsvProviderProvider<?> benchmarkResultWildcard : TestUtil
				.getCsvProviderProviderFromUltimateResults(resultService.getResults(), mBenchmark)) {
			final ICsvProviderProvider<Object> benchmarkResult = (ICsvProviderProvider<Object>) benchmarkResultWildcard;
			final ICsvProvider<Object> benchmarkCsv = benchmarkResult.createCvsProvider();
			final ICsvProvider<Object> benchmarkCsvWithRunDefinition = ColumnDefinitionUtil.prefixCsvProvider(
					ultimateRunDefinition, threeValuedResult, category, message, benchmarkCsv, a -> a);
			add(benchmarkCsvWithRunDefinition);
		}
	}

	private void add(final ICsvProvider<Object> benchmarkCsvWithRunDefinition) {
		mCsvProvider = CsvUtils.concatenateRows(mCsvProvider, benchmarkCsvWithRunDefinition);
	}
}
