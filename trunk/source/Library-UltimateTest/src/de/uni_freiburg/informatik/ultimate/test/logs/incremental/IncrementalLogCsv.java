/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.test.logs.incremental;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinitionUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Incremental log in which for each test all BenchmarkResults in .csv are logged.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class IncrementalLogCsv extends DefaultIncrementalLogfile {

	private final Class<? extends ICsvProviderProvider<? extends Object>> mBenchmark;
	private boolean mFirstEntry;

	public IncrementalLogCsv(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Class<? extends ICsvProviderProvider<? extends Object>> benchmarkClass) {
		super(ultimateTestSuite);
		mBenchmark = benchmarkClass;
		mFirstEntry = true;
	}

	@Override
	public String getDescriptiveLogName() {
		return "CsvLog-" + mBenchmark.getSimpleName();
	}

	@Override
	public void addEntryPreStart(final UltimateRunDefinition runDef, final ILogger testLogger) {
		// nothing is written before the start of a test
	}

	@Override
	public void addEntryPostCompletion(final UltimateRunDefinition runDef, final TestResult result,
			final String resultCategory, final String resultMessage, final IUltimateServiceProvider services,
			final ILogger testLogger) {
		final StringBuilder sb =
				addResult(runDef, result, resultCategory, resultMessage, services.getResultService().getResults());
		if (sb.length() > 0) {
			writeToFile(sb.toString(), testLogger);
		}
	}

	@Override
	public String getFilenameExtension() {
		return "-incremental.csv";
	}

	private StringBuilder addResult(final UltimateRunDefinition ultimateRunDefinition,
			final TestResult threeValuedResult, final String category, final String message,
			final Map<String, List<IResult>> results) {

		ICsvProvider<Object> combinedProvider = new SimpleCsvProvider<>(Collections.emptyList());
		final List<ICsvProviderProvider<?>> csvProviders =
				ResultUtil.getCsvProviderProviderFromUltimateResults(results, mBenchmark).stream()
						.map(a -> (ICsvProviderProvider<?>) a).collect(Collectors.toList());

		for (final ICsvProviderProvider<?> csvProvider : csvProviders) {
			final ICsvProvider<?> benchmarkCsv = csvProvider.createCsvProvider();
			final ICsvProvider<?> benchmarkCsvWithRunDefinition = ColumnDefinitionUtil
					.prefixCsvProvider(ultimateRunDefinition, threeValuedResult, category, message, benchmarkCsv);
			combinedProvider = CsvUtils.concatenateRowsUnchecked(combinedProvider, benchmarkCsvWithRunDefinition);
		}
		if (combinedProvider.isEmpty()) {
			return new StringBuilder();
		}
		final StringBuilder rtr = combinedProvider.toCsv(null, null, mFirstEntry);
		mFirstEntry = false;
		return rtr;
	}
}
