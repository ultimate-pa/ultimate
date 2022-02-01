package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.tacasminimization;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderColumnFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRounding;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRowFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderTransformerCombinator;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderTransformer;

/**
 * Test class to produce benchmark results.
 * <p>
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, and puts all
 * remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class PrepareOfflineCsv {
	private static final String EXTENSION = ".csv";
	private static final String INPUT_FILE_NAME = "AutomizerOffline";
	private static final String OUTPUT_FULL_FILE_NAME = "AutomizerOfflineFull";
	private static final String OUTPUT_PARTITIONED_FILE_NAME = "AutomizerOfflinePartitioned";
	private static final String OUTPUT_AGGREGATED_FILE_NAME = "AutomizerOfflineAggregated";
	private static final String COUNT = "Count";
	private static final String AGGREGATION = "Aggregation";
	private static final int[] THRESHOLDS = new int[] { 250, 1000, 4000, 16000 };
	private static final boolean VERBOSE = false;
	
	private static final String TRANSITIONS_RETURN_OUTPUT = "TRANSITIONS_RETURN_OUTPUT";
	private static final String TRANSITIONS_RETURN_INPUT = "TRANSITIONS_RETURN_INPUT";
	private static final String TRANSITIONS_CALL_OUTPUT = "TRANSITIONS_CALL_OUTPUT";
	private static final String TRANSITIONS_CALL_INPUT = "TRANSITIONS_CALL_INPUT";
	private static final String TRANSITIONS_INTERNAL_OUTPUT = "TRANSITIONS_INTERNAL_OUTPUT";
	private static final String TRANSITIONS_INTERNAL_INPUT = "TRANSITIONS_INTERNAL_INPUT";
	private static final String TIME_SOLVING = "TIME_SOLVING";
	private static final String TIME_PREPROCESSING = "TIME_PREPROCESSING";
	private static final String STATES_REDUCTION_RELATIVE = "STATES_REDUCTION_RELATIVE";
	private static final String STATES_REDUCTION_ABSOLUTE = "STATES_REDUCTION_ABSOLUTE";
	private static final String SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS = "SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS";
	private static final String RUNTIME_TOTAL = "RUNTIME_TOTAL";
	private static final String RESULT_TRANSITIONS = "RESULT_TRANSITIONS";
	private static final String RESULT_NONDETERMINISTIC_STATES = "RESULT_NONDETERMINISTIC_STATES";
	private static final String REMOVED_TRANSITIONS = "REMOVED_TRANSITIONS";
	private static final String NUMBER_OF_CLAUSES = "NUMBER_OF_CLAUSES";
	private static final String NUMBER_OF_VARIABLES = "NUMBER_OF_VARIABLES";
	private static final String BUCHI_TRANSITIONS = "BUCHI_TRANSITIONS";
	private static final String BUCHI_NONDETERMINISTIC_STATES = "BUCHI_NONDETERMINISTIC_STATES";
	private static final String ALPHABET_SIZE_RETURN = "ALPHABET_SIZE_RETURN";
	private static final String ALPHABET_SIZE_CALL = "ALPHABET_SIZE_CALL";
	private static final String ALPHABET_SIZE_INTERNAL = "ALPHABET_SIZE_INTERNAL";
	private static final String STATES_OUTPUT = "STATES_OUTPUT";
	private static final String STATES_INPUT = "STATES_INPUT";
	private static final String FILE = "File";
	
	private PrepareOfflineCsv() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME + EXTENSION);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		final List<ICsvProviderTransformer<String>> transformers = new ArrayList<>();
		final CsvProviderTransformerCombinator<String> transformer =
				new CsvProviderTransformerCombinator<>(transformers);
		
		transformers.add(getOperationFilter());
		transformers.add(getInterestingColumnFilter());
		transformers.add(getNonNullFilter());
		transformers.add(getNondetTransformer());
		
		// full table
		final ICsvProvider<String> fullTable = transformer.transform(input);
		writeCsvToFile(fullTable, OUTPUT_FULL_FILE_NAME, false);
		
		// separated tables
		final String statesColumn = STATES_INPUT;
		final CsvProviderPartition<String> partition = new CsvProviderPartition<>(fullTable, statesColumn, THRESHOLDS);
		final CsvProviderAggregator<String> csvProviderAggregator = getStatesAggregation();
		final CsvProviderRounding<String> csvProviderRound = getRounding();
		int i = 0;
		final List<ICsvProvider<String>> aggregatedCsvs = new ArrayList<>();
		for (final ICsvProvider<String> csv : partition.getCsvs()) {
			writeCsvToFile(csv, OUTPUT_PARTITIONED_FILE_NAME + i, false);
			
			// aggregate
			final ICsvProvider<String> aggregatedCsv = csvProviderAggregator.transform(csv);
			
			// round
			final ICsvProvider<String> roundedCsv = csvProviderRound.transform(aggregatedCsv);
			
			writeCsvToFile(roundedCsv, OUTPUT_AGGREGATED_FILE_NAME + i, true);
			
			aggregatedCsvs.add(roundedCsv);
			
			++i;
		}
		writeCsvToFile(new CsvProviderPartition<>(aggregatedCsvs).toCsvProvider(), OUTPUT_AGGREGATED_FILE_NAME, true);
	}
	
	private static CsvProviderRounding<String> getRounding() {
		return new CsvProviderRounding<>(0);
	}
	
	private static ICsvProviderTransformer<String> getOperationFilter() {
		final String[] allowedOperations = new String[] { "minimizeNwaMaxSat2" };
		final Map<String, Set<String>> column2allowedValues = Collections.singletonMap(
				StatisticsType.OPERATION_NAME.toString(), new HashSet<>(Arrays.asList(allowedOperations)));
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowedValues));
	}
	
	private static ICsvProviderTransformer<String> getInterestingColumnFilter() {
		final String[] forbiddenNames = new String[] { "Toolchain", "Settings", "ATS_ID", "BUCHI_ALPHABET_SIZE",
				"BUCHI_TRANSITION_DENSITY_MILLION", "OPERATION_NAME", "RESULT_TRANSITION_DENSITY_MILLION",
				"RESULT_ALPHABET_SIZE" };
		final CsvProviderColumnFilter.NameFilter forbiddenNamesFilter = new CsvProviderColumnFilter.NameFilter(
				new HashSet<>(Arrays.asList(forbiddenNames)));
		return new CsvProviderColumnFilter<>(x -> !x.isEmpty() && !forbiddenNamesFilter.test(x));
	}
	
	private static ICsvProviderTransformer<String> getNonNullFilter() {
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllEntriesNonNullFilter<>());
	}
	
	private static ICsvProviderTransformer<String> getNondetTransformer() {
		return new NondeterminismToBooleanTransformer();
	}
	
	private static CsvProviderAggregator<String> getStatesAggregation() {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put(FILE, Aggregation.IGNORE);
		
		column2aggregation.put(ALPHABET_SIZE_INTERNAL, Aggregation.AVERAGE);
		column2aggregation.put(ALPHABET_SIZE_CALL, Aggregation.AVERAGE);
		column2aggregation.put(ALPHABET_SIZE_RETURN, Aggregation.AVERAGE);
		column2aggregation.put(BUCHI_NONDETERMINISTIC_STATES, Aggregation.SUM);
		column2aggregation.put(BUCHI_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(NUMBER_OF_VARIABLES, Aggregation.AVERAGE);
		column2aggregation.put(NUMBER_OF_CLAUSES, Aggregation.AVERAGE);
		column2aggregation.put(REMOVED_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(RESULT_NONDETERMINISTIC_STATES, Aggregation.AVERAGE);
		column2aggregation.put(RESULT_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(RUNTIME_TOTAL, Aggregation.AVERAGE);
		column2aggregation.put(SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS, Aggregation.AVERAGE);
		column2aggregation.put(STATES_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(STATES_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(STATES_REDUCTION_ABSOLUTE, Aggregation.AVERAGE);
		column2aggregation.put(STATES_REDUCTION_RELATIVE, Aggregation.AVERAGE);
		column2aggregation.put(TIME_PREPROCESSING, Aggregation.AVERAGE);
		column2aggregation.put(TIME_SOLVING, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_INTERNAL_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_INTERNAL_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_CALL_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_CALL_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_RETURN_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_RETURN_OUTPUT, Aggregation.AVERAGE);
		
		return new CsvProviderAggregator<>(column2aggregation, COUNT);
	}
	
	private static void writeCsvToFile(final ICsvProvider<String> csv, final String fileName,
			final boolean aggregation) {
		final StringBuilder predefinedBuilder = new StringBuilder();
		if (aggregation) {
			predefinedBuilder.append(AGGREGATION);
		}
		final StringBuilder builder = csv.toCsv(predefinedBuilder, ",", true);
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
	 * This transformer replaces non-zero values in a specific column by the value {@code 1} (one), i.e., making this
	 * column of type Boolean.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class NondeterminismToBooleanTransformer implements ICsvProviderTransformer<String> {
		public NondeterminismToBooleanTransformer() {
			// nothing to do
		}
		
		@Override
		public ICsvProvider<String> transform(final ICsvProvider<String> csv) {
			final int columnIndex = csv.getColumnTitles().indexOf(BUCHI_NONDETERMINISTIC_STATES);
			final int rows = csv.getRowHeaders().size();
			for (int i = 0; i < rows; ++i) {
				final List<String> row = csv.getRow(i);
				final String entry = row.get(columnIndex);
				if (!"0".equals(entry)) {
					row.set(columnIndex, "1");
				}
			}
			return csv;
		}
	}
}
