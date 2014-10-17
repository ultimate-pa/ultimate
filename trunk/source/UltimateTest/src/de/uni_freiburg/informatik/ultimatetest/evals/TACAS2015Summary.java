package de.uni_freiburg.informatik.ultimatetest.evals;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;
import de.uni_freiburg.informatik.ultimatetest.util.Util.IMapReduce;
import de.uni_freiburg.informatik.ultimatetest.util.Util.IReduce;

/**
 * 
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class TACAS2015Summary extends NewTestSummary {

	public enum Aggregate {
		Sum, Max, Average, Ignore
	}

	private final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> mBenchmarks;
	private final LinkedHashMap<UltimateRunDefinition, ICsvProvider<?>> mCsvProvider;
	private int mCsvConversionGoneWrong;
	private final List<ColumnDefinition> mColumnDefinitions;
	private final int mLatexTableHeaderCount;

	public TACAS2015Summary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite);
		mBenchmarks = benchmarks;
		mCsvProvider = new LinkedHashMap<>();
		mColumnDefinitions = Arrays.asList(columnDefinitions);
		mLatexTableHeaderCount = Util.reduce(mColumnDefinitions, new IMapReduce<Integer, ColumnDefinition>() {
			@Override
			public Integer reduce(Integer lastValue, ColumnDefinition entry) {
				if (lastValue == null) {
					lastValue = 0;
				}
				return entry.getLatexTableTitle() != null ? lastValue + 1 : lastValue;
			}
		});
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

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		PartitionedResults results = partitionResults(mResults.entrySet());

		ICsvProvider<String> csvTotal = makePrintCsvProviderFromResults(results.All);
		printCsv(sb, "CSV", csvTotal);

		mCsvConversionGoneWrong = 0;

		sb.append("################################# Summary #######################").append(
				Util.getPlatformLineSeparator());
		sb.append(results);
		sb.append(Util.getPlatformLineSeparator());
		sb.append("CSV conversion gone wrong: ").append(mCsvConversionGoneWrong);
		sb.append(Util.getPlatformLineSeparator());
		sb.append(Util.getPlatformLineSeparator());

		// sb.append("################################# HTML #######################").append(
		// Util.getPlatformLineSeparator());
		//
		// CsvUtils.toHTML(csvSafe, sb, true, null);
		// sb.append(Util.getPlatformLineSeparator());
		// CsvUtils.toHTML(badCsv, sb, true, null);
		// sb.append(Util.getPlatformLineSeparator());

		sb.append("################################# Latex #######################").append(
				Util.getPlatformLineSeparator());

		makeTables(sb, results);

		return sb.toString();
	}

	private void makeTables(StringBuilder sb, PartitionedResults results) {

		Set<String> tools = Util.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getToolchain().getName();
			}
		});

		String br = Util.getPlatformLineSeparator();
		// define commands
		sb.append("\\newcommand{\\headcolor}{}").append(br);
		sb.append("\\newcommand{\\header}[1]{\\parbox{2.8em}{\\centering #1}\\headcolor}").append(br);
		sb.append("\\newcommand{\\folder}[1]{\\parbox{5em}{#1}}").append(br);

		for (final String tool : tools) {
			// make table header
			sb.append("\\begin{table}").append(br);
			sb.append("\\centering").append(br);
			sb.append("\\resizebox{\\linewidth}{!}{%").append(br);
			sb.append("\\begin{tabu} to \\linewidth {lcllc");
			for (int i = 0; i < mLatexTableHeaderCount; ++i) {
				sb.append("r");
			}
			sb.append("}").append(br);
			sb.append("\\toprule").append(br);
			sb.append("  \\header{}& ").append(br);
			sb.append("  \\header{\\#}&").append(br);
			sb.append("  \\header{Result}&").append(br);
			sb.append("  \\header{Variant}& ").append(br);
			sb.append("  \\header{Count}&").append(br);

			int i = 0;
			for (ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getLatexTableTitle() == null) {
					continue;
				}
				sb.append("  \\header{");
				sb.append(cd.getLatexTableTitle());
				sb.append("}");
				i++;
				if (i < mLatexTableHeaderCount) {
					sb.append("&");
				} else {
					sb.append("\\\\");
				}
				sb.append(br);
			}
			sb.append("  \\cmidrule(r){2-");
			sb.append(5 + mLatexTableHeaderCount);
			sb.append("}").append(br);

			// make table body
			PartitionedResults resultsPerTool = partitionResults(Util.where(results.All,
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().getName().equals(tool);
						}
					}));
			makeTableBody(sb, resultsPerTool, tool);

			// end table
			sb.append("\\end{tabu}}").append(br);
			sb.append("\\caption{Results for ").append(tool).append(".}").append(br);
			sb.append("\\end{table}").append(br);
		}
	}

	private void makeTableBody(StringBuilder sb, PartitionedResults results, String toolname) {
		// make header

		Set<String> folders = Util.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getInput().getParentFile().getName();
			}
		});

		int i = 0;
		for (final String folder : folders) {
			PartitionedResults resultsPerFolder = partitionResults(Util.where(results.All,
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getInput().getParentFile().getName().equals(folder);
						}
					}));
			i++;
			makeFolderRow(sb, resultsPerFolder, folder, i >= folders.size());
		}

	}

	private void makeFolderRow(StringBuilder sb, PartitionedResults results, String folder, boolean last) {
		String br = Util.getPlatformLineSeparator();
		final int resultRows = 4;

		List<String> variants = new ArrayList<>(Util.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getSettings().getName();
			}
		}));

		// folder name
		sb.append("\\multirow{");
		sb.append(variants.size() * resultRows);
		sb.append("}{*}{\\folder{");
		sb.append(folder);
		sb.append("}} &").append(br);

		// count expected unsafe & row header unsafe
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.ExpectedUnsafe / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Unsafe}} ").append(br);

		// results unsafe
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Unsafe, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// count expected safe & row header safe
		sb.append("& \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.ExpectedSafe / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Safe}} ").append(br);

		// results safe
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Safe, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// count total & row header total
		sb.append("& \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.All.size() / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Completed}} ").append(br);
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> completed = new ArrayList<>();
		completed.addAll(results.Safe);
		completed.addAll(results.Unsafe);
		for (int i = 0; i < variants.size(); ++i) {
			// this is the last in the foldoer row, so it gets a different
			// separator, hence false == isLast
			makeVariantEntry(sb, completed, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// row timeout
		sb.append("& & \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Timeout}} ").append(br);
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Timeout, variants.get(i), i == 0);
		}

		if (last) {
			sb.append("\\bottomrule").append(br);
			for (int i = 0; i < mLatexTableHeaderCount + 4; ++i) {
				sb.append("& ");
			}
			sb.append("\\\\").append(br);
		} else {
			sb.append("\\midrule").append(br);
		}
	}

	private void makeVariantEntry(StringBuilder sb, Collection<Entry<UltimateRunDefinition, ExtendedResult>> current,
			final String variant, boolean isFirst) {

		Collection<Entry<UltimateRunDefinition, ExtendedResult>> results = Util.where(current,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getKey().getSettings().getName().equals(variant);
					}
				});

		String br = Util.getPlatformLineSeparator();
		String sep = " & ";

		if (isFirst) {
			sb.append(sep);
		} else {
			sb.append(sep).append(sep).append(sep);
		}
		sb.append(variant);
		sb.append(sep);

		ICsvProvider<String> csv = makePrintCsvProviderFromResults(results);

		csv = CsvUtils.projectColumn(csv, Util.select(mColumnDefinitions, new IReduce<String, ColumnDefinition>() {
			@Override
			public String reduce(ColumnDefinition entry) {
				return entry.getColumnToKeep();
			}
		}));

		csv = reduceProvider(csv, Util.select(mColumnDefinitions, new IReduce<Aggregate, ColumnDefinition>() {
			@Override
			public Aggregate reduce(ColumnDefinition entry) {
				return entry.getManyRunsToOneRow();
			}
		}));

		csv = makeHumanReadable(csv);
		csv = CsvUtils.addColumn(csv, "Count", 0, Arrays.asList(new String[] { Integer.toString(results.size()) }));

		// make list of indices to ignore idx -> true / false
		boolean[] idx = new boolean[csv.getColumnTitles().size()];
		// because of count
		idx[0] = true;
		for (int i = 1; i < idx.length; ++i) {
			String currentHeader = csv.getColumnTitles().get(i);
			for (ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getColumnToKeep().equals(currentHeader)) {
					idx[i] = (cd.getLatexTableTitle() != null);
					break;
				}
			}
		}

		// one more because of Count
		int length = mLatexTableHeaderCount + 1;
		int i = 0;
		List<String> row = csv.getRow(0);
		if (row == null || row.size() == 0) {
			// no results in this category, just fill with empty fields
			for (; i < length; ++i) {
				sb.append(sep);
			}
		} else {
			for (String cell : row) {
				if (!idx[i]) {
					// skip this column, we dont want to print it
					i++;
					continue;
				}
				if (isInvalidForLatex(cell)) {
					sb.append("-");
				} else {
					sb.append(cell);
				}

				if (i < row.size() - 1) {
					sb.append(sep);
				}
				i++;
			}
		}
		sb.append("\\\\");
		sb.append(br);
	}

	/**
	 * Works only for TACAS tables
	 */
	private ICsvProvider<String> makeHumanReadable(ICsvProvider<String> csv) {

		ICsvProvider<String> newProvider = new SimpleCsvProvider<>(csv.getColumnTitles());
		List<String> newRow = new ArrayList<>();
		List<String> oldRow = csv.getRow(0);

		Collection<ConversionContext> conversionInfo = Util.select(mColumnDefinitions,
				new IReduce<ConversionContext, ColumnDefinition>() {
					@Override
					public ConversionContext reduce(ColumnDefinition entry) {
						return entry.getConversionContext();
					}
				});
		int i = 0;
		for (ConversionContext c : conversionInfo) {
			String cell = oldRow.get(i);
			newRow.add(c.makeHumanReadable(cell));
			++i;
		}

		newProvider.addRow(newRow);
		return newProvider;
	}

	private boolean isInvalidForLatex(String cell) {
		return cell == null || cell.contains("[");
	}

	private void printCsv(StringBuilder sb, String header, ICsvProvider<String> provider) {
		sb.append("################################# ").append(header).append(" #######################")
				.append(Util.getPlatformLineSeparator());
		provider.toCsv(sb, null);
		sb.append(Util.getPlatformLineSeparator());
		sb.append(Util.getPlatformLineSeparator());
	}

	private ICsvProvider<String> makePrintCsvProviderFromResults(
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> goodResults) {
		ICsvProvider<String> current = new SimpleCsvProvider<>(new ArrayList<String>());
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : goodResults) {
			ICsvProvider<?> provider = mCsvProvider.get(entry.getKey());
			if (provider == null) {
				mCsvConversionGoneWrong++;
				continue;
			}
			current = CsvUtils.concatenateRows(current,
					preparePrintProvider(provider, entry.getKey(), entry.getValue().Message));
		}
		return current;
	}

	private ICsvProvider<String> preparePrintProvider(ICsvProvider<?> provider, UltimateRunDefinition urd,
			String message) {
		List<String> names = new ArrayList<>(provider.getColumnTitles());
		for (String name : names) {
			int idx = name.indexOf("TraceCheckerBenchmark_");
			if (idx != -1) {
				provider.renameColumnTitle(name, name.substring(22));
			}
		}
		// provider.renameColumnTitle("ICC %", "ICC");
		provider = CsvUtils.projectColumn(provider,
				Util.select(mColumnDefinitions, new IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		// transform from multiple rows per UltimateTestCase to one (e.g. merge
		// the different benchmark types into one row)
		ICsvProvider<String> newProvider = reduceProvider(provider,
				Util.select(mColumnDefinitions, new IReduce<Aggregate, ColumnDefinition>() {
					@Override
					public Aggregate reduce(ColumnDefinition entry) {
						return entry.getSingleRunToOneRow();
					}
				}));
		newProvider = addUltimateRunDefinition(urd, message, newProvider);
		return newProvider;
	}

	private ICsvProvider<String> reduceProvider(ICsvProvider<?> provider, Collection<Aggregate> aggregates) {

		final HashSet<String> sum = new HashSet<>();
		final HashSet<String> max = new HashSet<>();
		final HashSet<String> avg = new HashSet<>();

		List<String> columnsToKeep = new ArrayList<>(Util.select(mColumnDefinitions,
				new IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		int i = 0;
		for (Aggregate aggregate : aggregates) {
			switch (aggregate) {
			case Average:
				avg.add(columnsToKeep.get(i));
				break;
			case Max:
				max.add(columnsToKeep.get(i));
				break;
			case Sum:
				sum.add(columnsToKeep.get(i));
				break;
			default:
				break;
			}
			++i;
		}

		ICsvProvider<String> newProvider = CsvUtils.convertComplete(provider,
				new IExplicitConverter<ICsvProvider<?>, ICsvProvider<String>>() {
					@Override
					public ICsvProvider<String> convert(ICsvProvider<?> input) {
						ICsvProvider<String> rtr = new SimpleCsvProvider<>(input.getColumnTitles());
						List<String> newRow = new ArrayList<>();

						int idx = 0;

						for (String columnTitle : input.getColumnTitles()) {
							String finalValue = null;
							BigDecimal numberValue = BigDecimal.ZERO;
							List<String> cells = new ArrayList<>();

							for (List<?> row : input.getTable()) {
								Object cell = row.get(idx);
								if (cell != null) {
									cells.add(cell.toString());
								}
							}

							if (cells.isEmpty()) {
								finalValue = "-";

							} else if (sum.contains(columnTitle)) {
								for (String cell : cells) {
									try {
										numberValue = numberValue.add(new BigDecimal((String) cell));
										finalValue = numberValue.toString();
									} catch (Exception ex) {
										finalValue = cell.toString();
									}
								}
							} else if (max.contains(columnTitle)) {
								for (String cell : cells) {
									try {
										numberValue = numberValue.max(new BigDecimal((String) cell));
										finalValue = numberValue.toString();
									} catch (Exception ex) {
										finalValue = cell.toString();
									}
								}
							} else if (avg.contains(columnTitle)) {
								int size = cells.size();
								for (String cell : cells) {
									try {
										numberValue = numberValue.add(new BigDecimal((String) cell));
										finalValue = numberValue.divide(new BigDecimal(size), 5, RoundingMode.HALF_UP)
												.toString();
									} catch (Exception ex) {
										finalValue = cell.toString();
									}
								}
							} else {
								for (String cell : cells) {
									finalValue = cell;
								}
							}
							idx++;
							newRow.add(finalValue);
						}
						rtr.addRow(newRow);
						return rtr;
					}
				});
		return newProvider;
	}

	private ICsvProvider<String> addUltimateRunDefinition(UltimateRunDefinition ultimateRunDefinition, String message,
			ICsvProvider<String> benchmark) {
		List<String> resultColumns = new ArrayList<>();
		resultColumns.add("Folder");
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.add("Message");
		resultColumns.addAll(benchmark.getColumnTitles());
		ICsvProvider<String> result = new SimpleCsvProvider<>(resultColumns);
		int rows = benchmark.getRowHeaders().size();
		for (int i = 0; i < rows; i++) {
			List<String> resultRow = new ArrayList<>();
			resultRow.add(ultimateRunDefinition.getInput().getParentFile().getName());
			resultRow.add(ultimateRunDefinition.getInput().getName());
			resultRow.add(ultimateRunDefinition.getSettings().getName());
			resultRow.add(ultimateRunDefinition.getToolchain().getName());
			resultRow.add(message);
			resultRow.addAll(benchmark.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

}
