package de.uni_freiburg.informatik.ultimatetest.summaries.tacasminimization;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRounding;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRowFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderScale;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderScale.ScaleMode;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Test class to produce benchmark results.
 * <p>
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, and puts all
 * remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class PrepareOnlineCsv {
	private static final String COMBINATOR_ONLY = "Combination only";
	private static final String COMBINATOR = "NWA_COMBINATOR_MULTI_DEFAULT.epf";
	private static final String NONE = "NONE.epf";
	private static final String SETTINGS_PREFIX =
			"/mnt/storage/ultimate/trunk/examples/settings/automizer/minimization/TreeInterpolants-";
	private static final String MINIMIZATON_ATTEMPTS_RELATIVE = "MinimizatonAttemptsRelative";
	private static final String MINIMIZATON_ATTEMPTS = "MinimizatonAttempts";
	private static final String STATES_REMOVED_BY_MINIMIZATION = "StatesRemovedByMinimization";
	private static final String OVERALL_ITERATIONS = "OverallIterations";
	private static final String OVERALL_TIME = "OverallTime";
	private static final String SETTING = "Settings";
	private static final String FILE = "File";
	
	private static final double HUNDRED = 100.0;
	
	private static final String EXTENSION = ".csv";
	private static final String INPUT_FILE_NAME = "AutomizerOnline";
	private static final String OUTPUT_AGGREGATED_FILE_NAME = "AutomizerOnlineAggregated";
	private static final String COUNT = "Count";
	private static final Double SCALING = Double.valueOf(1_000_000.0);
	private static final boolean VERBOSE = false;
	
	private PrepareOnlineCsv() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME + EXTENSION);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		// partition table by example
		final CsvProviderPartition<String> partitionByExample = getExamplePartition(input);
		final CsvProviderPartition<String> partitionByExampleCopy = partitionByExample.copy();
		
		// filter examples with at least one timeout/nontermination
		final ICsvProvider<String> bothFinished = getBothFinishedFilter(partitionByExample);
		
		// filter examples for which the combinator finished
		final ICsvProvider<String> combinationFinished = getCombinationFinishedFilter(partitionByExampleCopy);
		
		// partition table by setting
		final CsvProviderPartition<String> partitionBySettingBoth = getSettingsPartition(bothFinished);
		final CsvProviderPartition<String> partitionBySettingCombination = getSettingsPartition(combinationFinished);
		
		// aggregate data settings runs
		aggregate(partitionBySettingBoth);
		aggregate(partitionBySettingCombination);
		
		// add row header for combination only data
		final ICsvProvider<String> combinationOnly = partitionBySettingCombination.getCsvs().iterator().next();
		renameRowHeaders(combinationOnly, COMBINATOR_ONLY);
		
		final List<ICsvProvider<String>> csvs = new ArrayList<>(3);
		for (final ICsvProvider<String> csv : partitionBySettingBoth.getCsvs()) {
			csvs.add(csv);
		}
		csvs.add(combinationOnly);
		
		int i = 0;
		final CsvProviderScale csvProviderScale = getScaling();
		final CsvProviderRounding<String> csvProviderRound = getRounding();
		final List<ICsvProvider<String>> aggregatedCsvs = new ArrayList<>();
		for (final ICsvProvider<String> csv : csvs) {
			final ICsvProvider<String> scaledCsv = csvProviderScale.transform(csv);
			final ICsvProvider<String> roundedCsv = csvProviderRound.transform(scaledCsv);
			final ICsvProvider<String> addedColumnCsv =
					addRelativeColumn(roundedCsv, roundedCsv.getColumnTitles().indexOf(OVERALL_ITERATIONS),
							roundedCsv.getColumnTitles().indexOf(MINIMIZATON_ATTEMPTS), MINIMIZATON_ATTEMPTS_RELATIVE);
			renameRowHeaders(addedColumnCsv, null);
			
			writeCsvToFile(addedColumnCsv, OUTPUT_AGGREGATED_FILE_NAME + i);
			
			aggregatedCsvs.add(addedColumnCsv);
			
			++i;
		}
		writeCsvToFile(new CsvProviderPartition<>(aggregatedCsvs).toCsvProvider(), OUTPUT_AGGREGATED_FILE_NAME);
	}
	
	private static CsvProviderPartition<String> getExamplePartition(final ICsvProvider<String> csv) {
		final CsvProviderPartition<String> partitionByExample;
		final String statesColumn = FILE;
		partitionByExample = new CsvProviderPartition<>(csv, statesColumn);
		return partitionByExample;
	}
	
	private static ICsvProvider<String> getBothFinishedFilter(final CsvProviderPartition<String> partition) {
		partition.filterGroups(new TimeOutFilter());
		partition.filterGroups(new OnlyOneFilter());
		return partition.toCsvProvider();
	}
	
	private static ICsvProvider<String> getCombinationFinishedFilter(final CsvProviderPartition<String> partition) {
		final Map<String, Set<String>> column2allowedValues = new HashMap<>();
		column2allowedValues.put(SETTING, new HashSet<>(Arrays.asList(new String[] { SETTINGS_PREFIX + COMBINATOR })));
		final CsvProviderRowFilter<String> valuesFilter =
				new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowedValues));
		partition.transform(valuesFilter);
		
		partition.filterGroups(new TimeOutFilter());
		return partition.toCsvProvider();
	}
	
	private static CsvProviderPartition<String> getSettingsPartition(final ICsvProvider<String> settingsFiltered) {
		return new CsvProviderPartition<>(settingsFiltered, SETTING);
	}
	
	private static CsvProviderRounding<String> getRounding() {
		return new CsvProviderRounding<>(0);
	}
	
	private static CsvProviderScale getScaling() {
		final Map<String, Pair<Double, ScaleMode>> column2Scale = new HashMap<>();
		
		column2Scale.put(OVERALL_TIME, new Pair<>(SCALING, CsvProviderScale.ScaleMode.DIV_INT));
		
		return new CsvProviderScale(column2Scale);
	}
	
	private static void aggregate(final CsvProviderPartition<String> partitionBySetting) {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put(OVERALL_TIME, Aggregation.AVERAGE);
		column2aggregation.put(OVERALL_ITERATIONS, Aggregation.AVERAGE);
		column2aggregation.put(STATES_REMOVED_BY_MINIMIZATION, Aggregation.AVERAGE);
		column2aggregation.put(MINIMIZATON_ATTEMPTS, Aggregation.AVERAGE);
		
		partitionBySetting.transform(new CsvProviderAggregator<>(column2aggregation, COUNT));
	}
	
	@SuppressWarnings("squid:S1244")
	private static ICsvProvider<String> addRelativeColumn(final ICsvProvider<String> csv, final int baseColumnIndex,
			final int partColumnIndex, final String newColumnTitle) {
		final List<String> columnTitles = new ArrayList<>(csv.getColumnTitles().size() + 1);
		for (final String columnTitle : csv.getColumnTitles()) {
			columnTitles.add(columnTitle);
		}
		columnTitles.add(newColumnTitle);
		final int newColumnIndex = columnTitles.size() - 1;
		final ICsvProvider<String> result = new SimpleCsvProvider<>(columnTitles);
		
		final int rows = csv.getRowHeaders().size();
		for (int i = 0; i < rows; ++i) {
			final List<String> row = csv.getRow(i);
			final double base = Double.parseDouble(row.get(baseColumnIndex));
			final double part = Double.parseDouble(row.get(partColumnIndex));
			final String rel;
			if (part == 0.0) {
				rel = "-";
			} else {
				rel = Integer.toString((int) (HUNDRED * part / base));
			}
			final List<String> newRow = new ArrayList<>(row.size() + 1);
			for (final String entry : row) {
				newRow.add(entry);
			}
			newRow.add(newColumnIndex, rel);
			result.addRow(csv.getRowHeaders().get(i), newRow);
		}
		return result;
	}
	
	private static void renameRowHeaders(final ICsvProvider<String> csv, final String replaceString) {
		final List<String> rowHeaders = csv.getRowHeaders();
		for (int i = 0; i < rowHeaders.size(); ++i) {
			final String oldRowHeader = rowHeaders.get(i);
			final String shortened = oldRowHeader.replaceFirst(SETTINGS_PREFIX, "");
			final String newRowHeader;
			if (replaceString == null) {
				switch (shortened) {
					case NONE:
						newRowHeader = "Standalone";
						break;
					case COMBINATOR:
						newRowHeader = "Combination";
						break;
					case COMBINATOR_ONLY:
						continue;
					default:
						throw new IllegalArgumentException("Unknown setting: " + shortened);
				}
			} else {
				newRowHeader = replaceString;
			}
			rowHeaders.set(i, newRowHeader);
		}
	}
	
	private static void writeCsvToFile(final ICsvProvider<String> csv, final String fileName) {
		final StringBuilder builder = csv.toCsv(new StringBuilder(), ",");
		if (VERBOSE) {
			System.out.println(builder.toString());
		}
		final File file = new File(fileName + EXTENSION);
		try (BufferedWriter writer = new BufferedWriter(new FileWriter(file))) {
			writer.append(builder);
		} catch (final IOException e) {
			System.err.println("Writing file " + fileName + " failed.");
			e.printStackTrace();
		}
	}
	
	/**
	 * Checks whether the CSV has a {@code TIMEOUT} result.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class TimeOutFilter implements Predicate<ICsvProvider<String>> {
		private static final String TIMEOUT = "TIMEOUT";
		private static final String RESULT = "Result";
		
		public TimeOutFilter() {
			// nothing to do
		}
		
		@Override
		public boolean test(final ICsvProvider<String> csv) {
			int columnIndex = -1;
			// assume that all CSVs have the
			int index = 0;
			for (final String columnTitle : csv.getColumnTitles()) {
				if (RESULT.equals(columnTitle)) {
					columnIndex = index;
					break;
				}
				++index;
			}
			assert columnIndex != -1;
			
			final int rows = csv.getRowHeaders().size();
			for (int i = 0; i < rows; ++i) {
				final String entry = csv.getRow(i).get(columnIndex);
				if (TIMEOUT.equals(entry)) {
					return false;
				}
			}
			return true;
		}
	}
	
	/**
	 * Checks whether the CSV has two rows.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class OnlyOneFilter implements Predicate<ICsvProvider<String>> {
		public OnlyOneFilter() {
			// nothing to do
		}
		
		@Override
		public boolean test(final ICsvProvider<String> csv) {
			return csv.getRowHeaders().size() == 2;
		}
	}
}
