package de.uni_freiburg.informatik.ultimatetest.summaries.tacasminimization;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRounding;
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
	private static final String COMBINATOR_ALONE = "Combination only";
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
		final ICsvProvider<String> bothFinished = getBothFinishedFilter(partitionByExample);
		
		// partition table by setting
		final CsvProviderPartition<String> partitionBySetting = getSettingsPartition(bothFinished);
		
		// aggregate data settings runs
		aggregate(partitionBySetting);
		
		final List<ICsvProvider<String>> csvs = new ArrayList<>(3);
		for (final ICsvProvider<String> csv : partitionBySetting.getCsvs()) {
			csvs.add(csv);
		}
		
		final String[] settings = new String[] { NONE, COMBINATOR_ALONE, COMBINATOR };
		int i = 0;
		final CsvProviderRounding<String> csvProviderRound = getRounding();
		final List<ICsvProvider<String>> aggregatedCsvs = new ArrayList<>();
		for (final ICsvProvider<String> csv : csvs) {
			final ICsvProvider<String> roundedCsv = csvProviderRound.transform(csv);
			
			writeCsvToFile(roundedCsv, OUTPUT_AGGREGATED_FILE_NAME + i);
			
			aggregatedCsvs.add(csv);
			
			++i;
		}
		writeCsvToFile(new CsvProviderPartition(aggregatedCsvs).toCsvProvider(), OUTPUT_AGGREGATED_FILE_NAME);
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
	
	private static CsvProviderPartition<String> getSettingsPartition(final ICsvProvider<String> settingsFiltered) {
		return new CsvProviderPartition<>(settingsFiltered, SETTING);
	}
	
	private static CsvProviderRounding<String> getRounding() {
		return new CsvProviderRounding<>(0);
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
	
	/**
	 * Checks whether the CSV two rows.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class OnlyOneFilter implements Predicate<ICsvProvider<String>> {
		@Override
		public boolean test(final ICsvProvider<String> csv) {
			return csv.getRowHeaders().size() == 2;
		}
	}
}
