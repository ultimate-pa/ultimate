package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.tacasminimization;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderColumnFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderTransformerCombinator;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderTransformer;

/**
 * Test class to produce benchmark results.
 * <p>
 * Just aggregates a column to receive the mean.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class GetMean {
	private static final String EXTENSION = ".csv";
	private static final String INPUT_FILE_NAME = "AutomizerOfflineDet";
//	private static final String INPUT_FILE_NAME = "AutomizerOfflineNondet";
	private static final String OUTPUT_FULL_FILE_NAME_SUFFIX = "Aggregated";
	private static final String STATES_REDUCTION_RELATIVE = "STATES_REDUCTION_RELATIVE";
	private static final String TRANSITIONS_REDUCTION_RELATIVE = "TRANSITIONS_REDUCTION_RELATIVE";
	private static final boolean VERBOSE = true;
	
	private GetMean() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME + EXTENSION);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		final List<ICsvProviderTransformer<String>> transformers = new ArrayList<>();
		final CsvProviderTransformerCombinator<String> transformer =
				new CsvProviderTransformerCombinator<>(transformers);
		
		transformers.add(getColumnFilter());
		
		// full table
		final ICsvProvider<String> fullColumn = transformer.transform(input);
		
		// aggregate
		final ICsvProvider<String> mean = getStatesAggregation().transform(fullColumn);
		writeCsvToFile(mean, INPUT_FILE_NAME + OUTPUT_FULL_FILE_NAME_SUFFIX);
	}
	
	private static ICsvProviderTransformer<String> getColumnFilter() {
		final Collection<String> allowedNames =
				Arrays.asList(new String[] { STATES_REDUCTION_RELATIVE, TRANSITIONS_REDUCTION_RELATIVE });
		return new CsvProviderColumnFilter<>(new CsvProviderColumnFilter.NameFilter(allowedNames));
	}
	
	private static CsvProviderAggregator<String> getStatesAggregation() {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put(STATES_REDUCTION_RELATIVE, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_REDUCTION_RELATIVE, Aggregation.AVERAGE);
		
		return new CsvProviderAggregator<>(column2aggregation);
	}
	
	private static void writeCsvToFile(final ICsvProvider<String> csv, final String fileName) {
		final StringBuilder predefinedBuilder = new StringBuilder();
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
