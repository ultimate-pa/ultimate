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
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.NewTestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class BaseCsvProviderSummary extends NewTestSummary {

	protected final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> mBenchmarks;
	protected final LinkedHashMap<UltimateRunDefinition, ICsvProvider<?>> mCsvProvider;
	protected final List<ColumnDefinition> mColumnDefinitions;

	public BaseCsvProviderSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite);
		mBenchmarks = benchmarks;
		mCsvProvider = new LinkedHashMap<>();
		mColumnDefinitions = new ArrayList<ColumnDefinition>(Arrays.asList(columnDefinitions));
	}

	@SuppressWarnings("unchecked")
	@Override
	public void addResult(UltimateRunDefinition urd, TestResult threeValuedResult, String resultCategory, String message,
			String testname, IResultService resultService) {
		super.addResult(urd, threeValuedResult, resultCategory, message, testname, resultService);
		if (resultService == null) {
			return;
		}
		ICsvProvider<Object> aggregate = new SimpleCsvProvider<Object>(new ArrayList<String>());
		ICsvProvider<Object> current = null;
		for (final Class<? extends ICsvProviderProvider<? extends Object>> benchmark : mBenchmarks) {
			for (final ICsvProviderProvider<?> benchmarkResultWildcard : TestUtil.getCsvProviderProviderFromUltimateResults(
					resultService.getResults(), benchmark)) {
				current = (ICsvProvider<Object>) benchmarkResultWildcard.createCvsProvider();
				aggregate = CsvUtils.concatenateRows(aggregate, current);
			}
		}
		add(urd, aggregate);
	}

	private void add(UltimateRunDefinition urd, ICsvProvider<?> benchmarkCsvWithRunDefinition) {
		mCsvProvider.put(urd, benchmarkCsvWithRunDefinition);
	}

	protected ICsvProvider<String> makePrintCsvProviderFromResults(
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> results,
			List<ColumnDefinition> columnDefinitions) {
		ICsvProvider<String> current = new SimpleCsvProvider<>(new ArrayList<String>());
		for (final Entry<UltimateRunDefinition, ExtendedResult> entry : results) {
			final ICsvProvider<?> provider = mCsvProvider.get(entry.getKey());
			if (provider == null) {
				continue;
			}
			current = CsvUtils.concatenateRows(current, ColumnDefinitionUtil.preparePrintProvider(provider,
					entry.getKey(), entry.getValue(), columnDefinitions));
		}
		return current;
	}

}
