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

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ColumnDefinitionUtil {

	public static ICsvProvider<String> makeHumanReadable(final ICsvProvider<String> csv,
			final List<ColumnDefinition> columnDefinitions) {
		return makeHumanReadable(csv, columnDefinitions, 0);
	}

	public static ICsvProvider<String> makeHumanReadable(final ICsvProvider<String> csv,
			final List<ColumnDefinition> columnDefinitions, final int ignoreFirstNCells) {

		final ICsvProvider<String> newProvider = new SimpleCsvProvider<>(csv.getColumnTitles());

		final List<ConversionContext> conversionInfo = new ArrayList<>(
				CoreUtil.select(columnDefinitions, new CoreUtil.IReduce<ConversionContext, ColumnDefinition>() {
					@Override
					public ConversionContext reduce(final ColumnDefinition entry) {
						return entry.getConversionContext();
					}
				}));

		final int rows = csv.getRowHeaders().size();
		for (int i = 0; i < rows; ++i) {
			final List<String> newRow = new ArrayList<>();
			final List<String> oldRow = csv.getRow(i);

			int cellCount = 0;
			int contextCount = 0;
			for (final String cell : oldRow) {
				if (cellCount < ignoreFirstNCells) {
					newRow.add(cell);
				} else {
					final ConversionContext cc = conversionInfo.get(contextCount);
					newRow.add(cc.makeHumanReadable(cell));
					++contextCount;
				}
				++cellCount;
			}
			newProvider.addRow(newRow);
		}
		return newProvider;
	}

	public static ICsvProvider<String> reduceProvider(final ICsvProvider<?> provider,
			final Collection<ColumnDefinition.Aggregate> aggregates, final List<ColumnDefinition> columnDefinitions) {

		final HashSet<String> sum = new HashSet<>();
		final HashSet<String> max = new HashSet<>();
		final HashSet<String> avg = new HashSet<>();

		final List<String> columnsToKeep = new ArrayList<>(
				CoreUtil.select(columnDefinitions, new CoreUtil.IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(final ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		int i = 0;
		for (final ColumnDefinition.Aggregate aggregate : aggregates) {
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

		final ICsvProvider<String> newProvider = CsvUtils.convertComplete(provider,
				new IExplicitConverter<ICsvProvider<?>, ICsvProvider<String>>() {
					@Override
					public ICsvProvider<String> convert(final ICsvProvider<?> input) {
						final ICsvProvider<String> rtr = new SimpleCsvProvider<>(input.getColumnTitles());
						final List<String> newRow = new ArrayList<>();

						int idx = 0;

						for (final String columnTitle : input.getColumnTitles()) {
							String finalValue = null;
							BigDecimal numberValue = BigDecimal.ZERO;
							final List<String> cells = new ArrayList<>();

							for (final List<?> row : input.getTable()) {
								final Object cell = row.get(idx);
								if (cell != null) {
									cells.add(cell.toString());
								}
							}

							if (cells.isEmpty()) {
								finalValue = "-";

							} else if (sum.contains(columnTitle)) {
								for (final String cell : cells) {
									try {
										numberValue = numberValue.add(new BigDecimal(cell));
										finalValue = numberValue.toString();
									} catch (final Exception ex) {
										finalValue = cell;
									}
								}
							} else if (max.contains(columnTitle)) {
								for (final String cell : cells) {
									try {
										numberValue = numberValue.max(new BigDecimal(cell));
										finalValue = numberValue.toString();
									} catch (final Exception ex) {
										finalValue = cell.toString();
									}
								}
							} else if (avg.contains(columnTitle)) {
								final int size = cells.size();
								for (final String cell : cells) {
									try {
										numberValue = numberValue.add(new BigDecimal(cell));
										finalValue = numberValue.divide(new BigDecimal(size), 5, RoundingMode.HALF_UP)
												.toString();
									} catch (final Exception ex) {
										finalValue = cell.toString();
									}
								}
							} else {
								for (final String cell : cells) {
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

	/**
	 * Prepare a {@link ICsvProvider} for integration into one large provider that reflects a complete testsuite by
	 * doing the following.
	 * <ul>
	 * <li>Remove all columns that are not selected by the user.
	 * <li>Transform a provider with multiple rows into one with a single row by using the
	 * {@link ColumnDefinition#getSingleRunToOneRow()} method.
	 * <li>Add new columns containing information from {@link UltimateRunDefinition} and {@link ExtendedResult}.
	 * </ul>
	 * 
	 * @return A new {@link ICsvProvider} that contains one row per test case, only the user-selected columns, and
	 *         additional columns for run definition and test results.
	 */
	public static ICsvProvider<String> preparePrintProvider(ICsvProvider<?> provider, final UltimateRunDefinition urd,
			final ExtendedResult extendedResult, final List<ColumnDefinition> columnDefinitions) {

		// remove all columns that are marked for removal by column definitions
		provider = CsvUtils.projectColumn(provider,
				CoreUtil.select(columnDefinitions, new CoreUtil.IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(final ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		// transform from multiple rows per UltimateTestCase to one (e.g. merge
		// the different benchmark types into one row)
		ICsvProvider<String> newProvider = reduceProvider(provider, CoreUtil.select(columnDefinitions,
				new CoreUtil.IReduce<ColumnDefinition.Aggregate, ColumnDefinition>() {
					@Override
					public ColumnDefinition.Aggregate reduce(final ColumnDefinition entry) {
						return entry.getSingleRunToOneRow();
					}
				}), columnDefinitions);

		// add the ultimate run definition in the beginning
		newProvider = prefixCsvProvider(urd, extendedResult, newProvider);
		return newProvider;
	}

	/**
	 * Create a new ICsvProvider by prefixing every row with the contents of the {@link UltimateRunDefinition} and the
	 * result of the test (taken from {@link ExtendedResult}).
	 * 
	 * This method expects that the ICsvProvider belongs to a certain Ultimate run.
	 * 
	 */
	public static ICsvProvider<String> prefixCsvProvider(final UltimateRunDefinition urd,
			final ExtendedResult extendedResult, final ICsvProvider<String> provider) {
		// Note: Also change {@link #getColumnDefinitionForPrefix()} if you add a column here.
		final List<String> resultColumns = new ArrayList<>();
		resultColumns.add("Folder");
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.add("Result");
		resultColumns.add("Category");
		resultColumns.add("Message");
		resultColumns.addAll(provider.getColumnTitles());

		final ICsvProvider<String> result = new SimpleCsvProvider<>(resultColumns);
		final int rows = provider.getRowHeaders().size();
		for (int i = 0; i < rows; i++) {
			final List<String> resultRow = new ArrayList<>();
			resultRow.add(urd.getInputFileFolders());
			resultRow.add(urd.getInputFileNames());
			resultRow.add(urd.getSettingsName());
			resultRow.add(urd.getToolchain().getName());
			resultRow.add(extendedResult.getResult().toString());
			resultRow.add(extendedResult.getCategory());
			resultRow.add(extendedResult.getMessage());
			resultRow.addAll(provider.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

	/**
	 * Provide the column definitions for the additional columns introduced by
	 * {@link #prefixCsvProvider(UltimateRunDefinition, ExtendedResult, ICsvProvider)}.
	 */
	public static List<ColumnDefinition> getColumnDefinitionForPrefix() {
		final List<ColumnDefinition> rtr = new ArrayList<>();
		rtr.add(new ColumnDefinition("Folder", "Folder", ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore));
		rtr.add(new ColumnDefinition("File", "File", ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Settings", "Settings", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Toolchain", "Toolchain", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Result", "Result", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Category", "Category", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		rtr.add(new ColumnDefinition("Message", "Message", ConversionContext.Keep(), Aggregate.Ignore,
				Aggregate.Ignore));
		return rtr;
	}

	static void renameHeadersToLatexTitles(final ICsvProvider<String> csvTotal, final List<ColumnDefinition> columnDefinitions) {
		int i = 0;
		for (final String oldTitle : csvTotal.getColumnTitles()) {
			final String newTitle = columnDefinitions.get(i).getLatexTableTitle();
			if (newTitle != null) {
				csvTotal.renameColumnTitle(oldTitle, columnDefinitions.get(i).getLatexTableTitle());
			}
			i++;
		}
	}

}
