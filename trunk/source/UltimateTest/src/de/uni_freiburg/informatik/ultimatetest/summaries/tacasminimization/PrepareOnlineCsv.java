package de.uni_freiburg.informatik.ultimatetest.summaries.tacasminimization;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRowFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;

/**
 * Test class to produce benchmark results.
 * <p>
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, and puts all
 * remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class PrepareOnlineCsv {
	private static final String COMBINATOR = "Combination";
	private static final String NONE = "Standalone";
	private static final String FILE = "File";
	private static final String SETTING = "Settings";
	
	private static final String EXTENSION = ".csv";
	private static final String INPUT_FILE_NAME = "AutomizerOnline";
	private static final String OUTPUT_FULL_FILE_NAME = "AutomizerOnlineFull";
	private static final String OUTPUT_AGGREGATED_FILE_NAME = "AutomizerOnlineAggregated";
	private static final String COUNT = "Count";
	private static final boolean VERBOSE = true;
	
	private PrepareOnlineCsv() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME + EXTENSION);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		// TODO what about runs with 1 iteration? table contains "null" values due to this issue
		
		// partition table by example
		final CsvProviderPartition<String> partitionByExample = getExamplePartition(input);
		
		// filter examples with at least one timeout
		final ICsvProvider<String> noTimeOuts = getNoTimeoutFilter(partitionByExample);
		
		// partition table by setting
		final ICsvProvider<String> settingsFiltered = getSettingsFilter(noTimeOuts);
		
		final CsvProviderPartition<String> partitionBySetting = getSettingsPartition(settingsFiltered);
		aggregate(partitionBySetting);
		
		final String[] settings = new String[] { NONE, COMBINATOR };
		int i = 0;
		for (final ICsvProvider<String> csv : partitionBySetting.getCsvs()) {
			writeCsvToFile(csv, OUTPUT_AGGREGATED_FILE_NAME + settings[i]);
			
			++i;
		}
		
		System.out.println(settingsFiltered.toCsv(null, ","));
//		writeCsvToFile(new CsvProviderPartition(aggregatedCsvs).toCsvProvider(), OUTPUT_AGGREGATED_FILE_NAME);
	}
	
	private static CsvProviderPartition<String> getExamplePartition(final ICsvProvider<String> csv) {
		final CsvProviderPartition<String> partitionByExample;
		final String statesColumn = FILE;
		partitionByExample = new CsvProviderPartition<>(csv, statesColumn);
		return partitionByExample;
	}
	
	private static ICsvProvider<String> getNoTimeoutFilter(final CsvProviderPartition<String> partition) {
		partition.filterGroups(new TimeOutFilter());
		return partition.toCsvProvider();
	}
	
	private static ICsvProvider<String> getSettingsFilter(final ICsvProvider<String> csv) {
		final Map<String, Set<String>> column2allowed = new HashMap<>();
		final CsvProviderRowFilter<String> settingsFilter =
				new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowed));
		return settingsFilter.transform(csv);
	}
	
	private static CsvProviderPartition<String> getSettingsPartition(final ICsvProvider<String> settingsFiltered) {
		return new CsvProviderPartition<>(settingsFiltered, SETTING);
	}
	
	private static void aggregate(final CsvProviderPartition<String> partitionBySetting) {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put("OverallTime", Aggregation.AVERAGE);
		column2aggregation.put("OverallIterations", Aggregation.AVERAGE);
		column2aggregation.put("StatesRemovedByMinimization", Aggregation.AVERAGE);
		column2aggregation.put("MinimizatonAttempts", Aggregation.AVERAGE);
		
		partitionBySetting.transform(new CsvProviderAggregator<>(column2aggregation, COUNT));
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
}
