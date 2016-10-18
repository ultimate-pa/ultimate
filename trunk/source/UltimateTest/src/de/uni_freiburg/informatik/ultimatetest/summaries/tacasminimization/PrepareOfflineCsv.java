package de.uni_freiburg.informatik.ultimatetest.summaries.tacasminimization;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderColumnFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
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
public class PrepareOfflineCsv {
	private static final String INPUT_FILE_NAME = "AutomizerOffline.csv";
	
	private PrepareOfflineCsv() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		final List<ICsvProviderTransformer<String>> transformers = new ArrayList<>();
		final CsvProviderTransformerCombinator<String> transformer =
				new CsvProviderTransformerCombinator<>(transformers);
		
		transformers.add(getOperationFilter());
		transformers.add(getInterestingColumnFilter());
		transformers.add(getNonNullFilter());
		
		final ICsvProvider<String> result = transformer.transform(input);
		final StringBuilder builder = new StringBuilder();
		System.out.println(result.toCsv(builder, ",").toString());
	}
	
	private static ICsvProviderTransformer<String> getOperationFilter() {
		final String[] allowedOperations = new String[] { "minimizeNwaMaxSat2" };
		final Map<String, Set<String>> column2allowedValues = Collections.singletonMap(
				StatisticsType.OPERATION_NAME.toString(), new HashSet<>(Arrays.asList(allowedOperations)));
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowedValues));
	}
	
	private static ICsvProviderTransformer<String> getInterestingColumnFilter() {
		final String[] forbiddenNames =
				new String[] { "Toolchain", "SETTINGS", "ATS_ID", "BUCHI_ALPHABET_SIZE",
						"BUCHI_TRANSITION_DENSITY_MILLION", "OPERATION_NAME", };
		final CsvProviderColumnFilter.NameFilter forbiddenNamesFilter = new CsvProviderColumnFilter.NameFilter(
				new HashSet<>(Arrays.asList(forbiddenNames)));
		return new CsvProviderColumnFilter<>(x -> !x.isEmpty() && !forbiddenNamesFilter.test(x));
	}
	
	private static ICsvProviderTransformer<String> getNonNullFilter() {
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllEntriesNonNullFilter<>());
	}
}
