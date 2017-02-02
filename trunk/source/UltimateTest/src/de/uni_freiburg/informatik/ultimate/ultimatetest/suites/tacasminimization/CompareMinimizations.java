package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.tacasminimization;

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
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, aggregates data by
 * minimization method, and puts all remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class CompareMinimizations {
	private static final String EXTENSION = ".csv";
	private static final String INPUT_FILE_NAME = "REPLACE_ME";
	private static final String OUTPUT_FULL_FILE_NAME = INPUT_FILE_NAME + "_full";
	private static final String OUTPUT_PARTITIONED_FILE_NAME = INPUT_FILE_NAME + "_partitioned";
	private static final String OUTPUT_AGGREGATED_FILE_NAME = INPUT_FILE_NAME + "_aggregated";
	private static final String OUTPUT_AGGREGATED_ALL_FILE_NAME = OUTPUT_AGGREGATED_FILE_NAME + "_all";
	private static final String COUNT = "Count";
	private static final String AGGREGATION = "Aggregation";
	private static final int NUMBER_OF_OPERATIONS = 8;
	private static final boolean ROUNDING = false;
	private static final boolean VERBOSE = false;
	
	private static final String FILE = "File";
	private static final String OPERATION_NAME = "OPERATION_NAME";
	private static final String BUCHI_NONDETERMINISTIC_STATES = "BUCHI_NONDETERMINISTIC_STATES";
	private static final String BUCHI_TRANSITION_DENSITY_MILLION = "BUCHI_TRANSITION_DENSITY_MILLION";
	private static final String RUNTIME_TOTAL = "RUNTIME_TOTAL";
	private static final String SIZE_GAME_AUTOMATON = "SIZE_GAME_AUTOMATON";
	private static final String SIZE_GAME_GRAPH = "SIZE_GAME_GRAPH";
	private static final String SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS = "SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS";
	private static final String STATES_INPUT = "STATES_INPUT";
	private static final String STATES_OUTPUT = "STATES_OUTPUT";
	private static final String STATES_REDUCTION_ABSOLUTE = "STATES_REDUCTION_ABSOLUTE";
	private static final String STATES_REDUCTION_RELATIVE = "STATES_REDUCTION_RELATIVE";
	private static final String TIME_PREPROCESSING = "TIME_PREPROCESSING";
	private static final String TIME_SOLVING = "TIME_SOLVING";
	
	private CompareMinimizations() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME + EXTENSION);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		// partition table by example
		final CsvProviderPartition<String> partitionByExample = getExamplePartition(input);
		partitionByExample.copy();
		
		System.out.println("A total of " + partitionByExample.size() + " programs were analyzed.");
		
		final List<ICsvProviderTransformer<String>> transformers = new ArrayList<>();
		final CsvProviderTransformerCombinator<String> transformer =
				new CsvProviderTransformerCombinator<>(transformers);
		
		transformers.add(getInterestingColumnFilter());
		transformers.add(getNonNullFilter());
		
		// full table
		final List<ICsvProvider<String>> examplesWithoutNulls = new ArrayList<>();
		for (final ICsvProvider<String> csv : partitionByExample.getCsvs()) {
			final ICsvProvider<String> csvOrEmpty = transformer.transform(csv);
			if (csvOrEmpty.getRowHeaders().size() == csv.getRowHeaders().size()) {
				if (csvOrEmpty.getRowHeaders().size() != NUMBER_OF_OPERATIONS) {
					System.err.println("In the following aggregation by example an operation is missing:");
					System.err.println(csv);
				}
				examplesWithoutNulls.add(csv);
			}
		}
		final ICsvProvider<String> fullTable = new CsvProviderPartition<>(examplesWithoutNulls).toCsvProvider();
		writeCsvToFile(fullTable, OUTPUT_FULL_FILE_NAME, false);
		
		// separated tables
		final CsvProviderPartition<String> partition = new CsvProviderPartition<>(fullTable, OPERATION_NAME);
		final CsvProviderAggregator<String> csvProviderAggregator = getOperationAggregation();
		final CsvProviderRounding<String> csvProviderRound = getRounding();
		final List<ICsvProvider<String>> aggregatedCsvs = new ArrayList<>();
		for (final ICsvProvider<String> csv : partition.getCsvs()) {
			final String operationName = getOperationName(csv);
			writeCsvToFile(csv, OUTPUT_PARTITIONED_FILE_NAME + operationName, false);
			
			// aggregate
			final ICsvProvider<String> aggregatedCsv = csvProviderAggregator.transform(csv);
			
			// round
			final ICsvProvider<String> roundedCsv;
			if (ROUNDING) {
				roundedCsv = csvProviderRound.transform(aggregatedCsv);
			} else {
				roundedCsv = aggregatedCsv;
			}
			
			writeCsvToFile(roundedCsv, OUTPUT_AGGREGATED_FILE_NAME + operationName, true);
			
			aggregatedCsvs.add(roundedCsv);
		}
		writeCsvToFile(new CsvProviderPartition<>(aggregatedCsvs).toCsvProvider(), OUTPUT_AGGREGATED_ALL_FILE_NAME,
				true);
	}
	
	private static String getOperationName(final ICsvProvider<String> csv) {
		return "_" + csv.getRow(0).get(csv.getColumnTitles().indexOf(OPERATION_NAME));
	}
	
	private static CsvProviderPartition<String> getExamplePartition(final ICsvProvider<String> csv) {
		final CsvProviderPartition<String> partitionByExample;
		final String statesColumn = FILE;
		partitionByExample = new CsvProviderPartition<>(csv, statesColumn);
		return partitionByExample;
	}
	
	private static CsvProviderRounding<String> getRounding() {
		return new CsvProviderRounding<>(0);
	}
	
	private static ICsvProviderTransformer<String> getInterestingColumnFilter() {
		final String[] allowedNames = new String[] { STATES_INPUT };
		final CsvProviderColumnFilter.NameFilter allowedNamesFilter = new CsvProviderColumnFilter.NameFilter(
				new HashSet<>(Arrays.asList(allowedNames)));
		return new CsvProviderColumnFilter<>(x -> !x.isEmpty() && allowedNamesFilter.test(x));
	}
	
	private static ICsvProviderTransformer<String> getNonNullFilter() {
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllEntriesNonNullFilter<>());
	}
	
	private static CsvProviderAggregator<String> getOperationAggregation() {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put(FILE, Aggregation.IGNORE);
		column2aggregation.put(BUCHI_NONDETERMINISTIC_STATES, Aggregation.IGNORE);
		column2aggregation.put(BUCHI_TRANSITION_DENSITY_MILLION, Aggregation.IGNORE);
		column2aggregation.put(OPERATION_NAME, Aggregation.IGNORE);
		column2aggregation.put(SIZE_GAME_AUTOMATON, Aggregation.IGNORE);
		column2aggregation.put(SIZE_GAME_GRAPH, Aggregation.IGNORE);
		column2aggregation.put(SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS, Aggregation.IGNORE);
		column2aggregation.put(STATES_REDUCTION_ABSOLUTE, Aggregation.IGNORE);
		column2aggregation.put(STATES_REDUCTION_RELATIVE, Aggregation.IGNORE);
		column2aggregation.put(TIME_PREPROCESSING, Aggregation.IGNORE);
		column2aggregation.put(TIME_SOLVING, Aggregation.IGNORE);
		
		column2aggregation.put(RUNTIME_TOTAL, Aggregation.AVERAGE);
		column2aggregation.put(STATES_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(STATES_OUTPUT, Aggregation.AVERAGE);
		
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
}
