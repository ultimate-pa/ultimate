package de.uni_freiburg.informatik.ultimatetest.summary;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ExtendedCsvConcatenator extends NewTestSummary {

	private final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> mBenchmarks;
	private final LinkedHashMap<UltimateRunDefinition, ICsvProvider<?>> mCsvProvider;

	public ExtendedCsvConcatenator(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks) {
		super(ultimateTestSuite);
		mBenchmarks = benchmarks;
		mCsvProvider = new LinkedHashMap<>();
	}

	@Override
	public void addResult(UltimateRunDefinition urd, TestResult threeValuedResult, String category, String message,
			String testname, IResultService resultService) {
		super.addResult(urd, threeValuedResult, category, message, testname, resultService);
		if (resultService == null) {
			return;
		}
		ICsvProvider<Object> aggregate = new SimpleCsvProvider<Object>(new ArrayList<String>());
		for (Class<? extends ICsvProviderProvider<? extends Object>> benchmark : mBenchmarks) {
			for (ICsvProviderProvider<?> benchmarkResultWildcard : Util.getCsvProviderProviderFromUltimateResults(resultService.getResults(),
					benchmark)) {
				aggregate = CsvUtils.concatenateRows(aggregate,
						(ICsvProvider<Object>) benchmarkResultWildcard.createCvsProvider());
			}
		}
		add(urd, aggregate);
	}

	private void add(UltimateRunDefinition urd, ICsvProvider<?> benchmarkCsvWithRunDefinition) {
		mCsvProvider.put(urd, benchmarkCsvWithRunDefinition);
	}

	private String[] columnsToKeep = new String[] { "Runtime (ns)", "Peak memory consumption (bytes)",
			"Max. memory available (bytes)",  "Overall iterations",
			"TraceCheckerBenchmark_NumberOfCodeBlocks", "TraceCheckerBenchmark_SizeOfPredicates",
			"TraceCheckerBenchmark_Conjuncts in SSA", "TraceCheckerBenchmark_Conjuncts in UnsatCore",
			"InterpolantCoveringCapability", "#iterations" };

	private String[] columnsToSum = new String[] { "Runtime (ns)", };

	private String[] columnsToMax = new String[] { "Peak memory consumption (bytes)", "Max. memory available (bytes)", };
	private int mCsvConversionGoneWrong;

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> goodResults = Util.where(mResults.entrySet(),
				new IMyPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().Result == TestResult.SUCCESS
								|| (entry.getValue().Result == TestResult.UNKNOWN && entry.getValue().Message
										.contains("Timeout"));
					}
				});
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> badResults = Util.where(mResults.entrySet(),
				new IMyPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return !(entry.getValue().Result == TestResult.SUCCESS || (entry.getValue().Result == TestResult.UNKNOWN && entry
								.getValue().Message.contains("Timeout")));
					}
				});

		mCsvConversionGoneWrong = 0;
		sb.append("################################# Good #######################").append(
				Util.getPlatformLineSeparator());
		ICsvProvider<String> goodCsv = makeOneCsvProvider(goodResults);
		goodCsv.toCsv(sb, null);

		sb.append(Util.getPlatformLineSeparator());
		sb.append(Util.getPlatformLineSeparator());

		sb.append("################################# Bad #######################").append(
				Util.getPlatformLineSeparator());
		ICsvProvider<String> badCsv = makeOneCsvProvider(badResults);
		badCsv.toCsv(sb, null);

		sb.append(Util.getPlatformLineSeparator());
		sb.append(Util.getPlatformLineSeparator());

		sb.append("################################# Total #######################").append(
				Util.getPlatformLineSeparator());
		sb.append("Success+Timeout: ").append(goodResults.size());
		sb.append(Util.getPlatformLineSeparator());
		sb.append("Failure+Unknown\\Timeout: ").append(mResults.size() - goodResults.size());
		sb.append(Util.getPlatformLineSeparator());
		sb.append("Total: ").append(mResults.size());
		sb.append(Util.getPlatformLineSeparator());
		sb.append("CSV conversion gone wrong: ").append(mCsvConversionGoneWrong);
		sb.append(Util.getPlatformLineSeparator());
		sb.append(Util.getPlatformLineSeparator());
		
		sb.append("################################# HTML #######################").append(
				Util.getPlatformLineSeparator());

		CsvUtils.toHTML(goodCsv, sb, true, null);
		sb.append(Util.getPlatformLineSeparator());
		CsvUtils.toHTML(badCsv, sb, true, null);
		sb.append(Util.getPlatformLineSeparator());

		sb.append("################################# Latex #######################").append(
				Util.getPlatformLineSeparator());
		return sb.toString();
	}

	private ICsvProvider<String> makeOneCsvProvider(Collection<Entry<UltimateRunDefinition, ExtendedResult>> goodResults) {
		ICsvProvider<String> current = new SimpleCsvProvider<>(new ArrayList<String>());
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : goodResults) {
			ICsvProvider<?> provider = mCsvProvider.get(entry.getKey());
			if (provider == null) {
				mCsvConversionGoneWrong++;
				continue;
			}
			current = CsvUtils.concatenateRows(current,
					prepareProvider(provider, entry.getKey(), entry.getValue().Message));
		}
		return current;
	}

	private ICsvProvider<String> prepareProvider(ICsvProvider<?> provider, UltimateRunDefinition urd, String message) {
		provider = CsvUtils.projectColumn(provider, columnsToKeep);
		ICsvProvider<String> newProvider = CsvUtils.convertComplete(provider,
				new IExplicitConverter<ICsvProvider<?>, ICsvProvider<String>>() {
					@Override
					public ICsvProvider<String> convert(ICsvProvider<?> provider) {
						ICsvProvider<?> input = CsvUtils.projectColumn(provider, columnsToKeep);
						ICsvProvider<String> rtr = new SimpleCsvProvider<>(input.getColumnTitles());
						List<String> newRow = new ArrayList<>();

						HashSet<String> sum = new HashSet<>(Arrays.asList(columnsToSum));
						HashSet<String> max = new HashSet<>(Arrays.asList(columnsToMax));

						int idx = 0;

						for (String columnTitle : input.getColumnTitles()) {
							String finalValue = null;

							if (sum.contains(columnTitle)) {
								int intValue = 0;
								double doubleValue = 0;
								for (List<?> row : input.getTable()) {
									Object cell = row.get(idx);
									if (cell == null) {
										continue;
									} else if (cell instanceof Double) {
										doubleValue += (Double) cell;
										finalValue = Double.toString(doubleValue);
									} else if (cell instanceof Integer) {
										intValue += (Integer) cell;
										finalValue = Integer.toString(intValue);
									} else {
										throw new UnsupportedOperationException();
									}
								}
							} else if (max.contains(columnTitle)) {
								int intValue = 0;
								double doubleValue = 0;
								for (List<?> row : input.getTable()) {
									Object cell = row.get(idx);
									if (cell == null) {
										continue;
									} else if (cell instanceof Double) {
										doubleValue = Math.max(doubleValue, (Double) cell);
										finalValue = Double.toString(doubleValue);
									} else if (cell instanceof Integer) {
										intValue = Math.max(intValue, (Integer) cell);
										finalValue = Integer.toString(intValue);
									} else {
										throw new UnsupportedOperationException();
									}
								}
							} else {
								for (List<?> row : input.getTable()) {
									Object cell = row.get(idx);
									if (cell == null) {
										continue;
									} else {
										finalValue = cell.toString();
									}
								}
							}
							idx++;
							newRow.add(finalValue);
						}
						rtr.addRow(newRow);
						return rtr;
					}
				});
		newProvider = addUltimateRunDefinition(urd, message, newProvider);
		return newProvider;
	}

	private ICsvProvider<String> addUltimateRunDefinition(UltimateRunDefinition ultimateRunDefinition, String message,
			ICsvProvider<String> benchmark) {
		List<String> resultColumns = new ArrayList<>();
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.add("Message");
		resultColumns.addAll(benchmark.getColumnTitles());
		ICsvProvider<String> result = new SimpleCsvProvider<>(resultColumns);
		int rows = benchmark.getRowHeaders().size();
		for (int i = 0; i < rows; i++) {
			List<String> resultRow = new ArrayList<>();

			resultRow.add(ultimateRunDefinition.getInput().getParentFile().getName() + File.separator
					+ ultimateRunDefinition.getInput().getName());
			resultRow.add(ultimateRunDefinition.getSettings().getName());
			resultRow.add(ultimateRunDefinition.getToolchain().getName());
			resultRow.add(message);
			resultRow.addAll(benchmark.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

}
