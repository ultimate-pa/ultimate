package de.uni_freiburg.informatik.ultimatetest.evals;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.evals.ColumnDefinition.Aggregate;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ColumnDefinitionUtil {

	public static ICsvProvider<String> makeHumanReadable(ICsvProvider<String> csv,
			List<ColumnDefinition> columnDefinitions) {
		return makeHumanReadable(csv, columnDefinitions, 0);
	}

	public static ICsvProvider<String> makeHumanReadable(ICsvProvider<String> csv,
			List<ColumnDefinition> columnDefinitions, int ignoreFirstNCells) {

		ICsvProvider<String> newProvider = new SimpleCsvProvider<>(csv.getColumnTitles());

		List<ConversionContext> conversionInfo = new ArrayList<>(CoreUtil.select(columnDefinitions,
				new CoreUtil.IReduce<ConversionContext, ColumnDefinition>() {
					@Override
					public ConversionContext reduce(ColumnDefinition entry) {
						return entry.getConversionContext();
					}
				}));

		int rows = csv.getRowHeaders().size();
		for (int i = 0; i < rows; ++i) {
			List<String> newRow = new ArrayList<>();
			List<String> oldRow = csv.getRow(i);

			int cellCount = 0;
			int contextCount = 0;
			for (String cell : oldRow) {
				if (cellCount < ignoreFirstNCells) {
					newRow.add(cell);
				} else {
					ConversionContext cc = conversionInfo.get(contextCount);
					newRow.add(cc.makeHumanReadable(cell));
					++contextCount;
				}
				++cellCount;
			}
			newProvider.addRow(newRow);
		}
		return newProvider;
	}

	public static ICsvProvider<String> reduceProvider(ICsvProvider<?> provider,
			Collection<ColumnDefinition.Aggregate> aggregates, List<ColumnDefinition> columnDefinitions) {

		final HashSet<String> sum = new HashSet<>();
		final HashSet<String> max = new HashSet<>();
		final HashSet<String> avg = new HashSet<>();

		List<String> columnsToKeep = new ArrayList<>(CoreUtil.select(columnDefinitions,
				new CoreUtil.IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		int i = 0;
		for (ColumnDefinition.Aggregate aggregate : aggregates) {
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

	public static ICsvProvider<String> preparePrintProvider(ICsvProvider<?> provider, UltimateRunDefinition urd,
			String message, List<ColumnDefinition> columnDefinitions) {
		List<String> names = new ArrayList<>(provider.getColumnTitles());
		for (String name : names) {
			int idx = name.indexOf("TraceCheckerBenchmark_");
			if (idx != -1) {
				provider.renameColumnTitle(name, name.substring(22));
			}
		}
		// remove all columns that are marked for removal by column definitions
		provider = CsvUtils.projectColumn(provider,
				CoreUtil.select(columnDefinitions, new CoreUtil.IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		// transform from multiple rows per UltimateTestCase to one (e.g. merge
		// the different benchmark types into one row)
		ICsvProvider<String> newProvider = reduceProvider(provider, CoreUtil.select(columnDefinitions,
				new CoreUtil.IReduce<ColumnDefinition.Aggregate, ColumnDefinition>() {
					@Override
					public ColumnDefinition.Aggregate reduce(ColumnDefinition entry) {
						return entry.getSingleRunToOneRow();
					}
				}), columnDefinitions);

		newProvider = prefixCsvProvider(urd, message, newProvider);
		return newProvider;
	}

	/**
	 * Create a new ICsvProvider by prefixing every row with the contents of the
	 * UltimateRunDefinition and an arbitrary message.
	 * 
	 * This method expects that the ICsvProvider belongs to a certain Ultimate
	 * run.
	 * 
	 * @param ultimateRunDefinition
	 * @param message
	 * @param provider
	 * @return
	 */
	public static ICsvProvider<String> prefixCsvProvider(UltimateRunDefinition urd, String message,
			ICsvProvider<String> provider) {
		List<String> resultColumns = new ArrayList<>();
		resultColumns.add("Folder");
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.add("Message");
		resultColumns.addAll(provider.getColumnTitles());

		ICsvProvider<String> result = new SimpleCsvProvider<>(resultColumns);
		int rows = provider.getRowHeaders().size();
		for (int i = 0; i < rows; i++) {
			List<String> resultRow = new ArrayList<>();
			resultRow.add(urd.getInput().getParentFile().getName());
			resultRow.add(urd.getInput().getName());
			resultRow.add(urd.getSettings().getName());
			resultRow.add(urd.getToolchain().getName());
			resultRow.add(message);
			resultRow.addAll(provider.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

	public static List<ColumnDefinition> getColumnDefinitionForPrefix() {
		List<ColumnDefinition> rtr = new ArrayList<>();
		rtr.add(new ColumnDefinition("Folder", "Folder", ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore));
		rtr.add(new ColumnDefinition("File", "File", ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Settings", "Settings", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Toolchain", "Toolchain", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Message", "Message", ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore));
		return rtr;
	}

	static void renameHeadersToLatexTitles(ICsvProvider<String> csvTotal, List<ColumnDefinition> columnDefinitions) {
		int i = 0;
		for (String oldTitle : csvTotal.getColumnTitles()) {
			String newTitle = columnDefinitions.get(i).getLatexTableTitle();
			if (newTitle != null) {
				csvTotal.renameColumnTitle(oldTitle, columnDefinitions.get(i).getLatexTableTitle());
			}
			i++;
		}
	}

}
