package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

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
	public void addResult(UltimateRunDefinition urd, TestResult threeValuedResult, String category, String message,
			String testname, IResultService resultService) {
		super.addResult(urd, threeValuedResult, category, message, testname, resultService);
		if (resultService == null) {
			return;
		}
		ICsvProvider<Object> aggregate = new SimpleCsvProvider<Object>(new ArrayList<String>());
		ICsvProvider<Object> current = null;
		for (Class<? extends ICsvProviderProvider<? extends Object>> benchmark : mBenchmarks) {
			for (ICsvProviderProvider<?> benchmarkResultWildcard : Util.getCsvProviderProviderFromUltimateResults(
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
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> goodResults) {
		ICsvProvider<String> current = new SimpleCsvProvider<>(new ArrayList<String>());
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : goodResults) {
			ICsvProvider<?> provider = mCsvProvider.get(entry.getKey());
			if (provider == null) {
				continue;
			}
			current = CsvUtils.concatenateRows(current, ColumnDefinitionUtil.preparePrintProvider(provider,
					entry.getKey(), entry.getValue().Message, mColumnDefinitions));
		}
		return current;
	}

}