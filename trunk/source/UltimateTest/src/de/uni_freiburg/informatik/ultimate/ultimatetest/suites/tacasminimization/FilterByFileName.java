package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.tacasminimization;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;

/**
 * Test class to produce benchmark results.
 * <p>
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, and puts all
 * remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class FilterByFileName {
	private FilterByFileName() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File("summary.csv");
		
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		final CsvProviderPartition<String> partition = new CsvProviderPartition<>(input, "File");
		final CsvProviderPartition<String> partitionCopy = partition.copy();
		
		partitionCopy.filterGroups(partitionCopy.new AllEntriesNonNullFilter());
		
		final ICsvProvider<String> output = partitionCopy.toCsvProvider();
		final StringBuilder builder = new StringBuilder();
		output.toCsv(builder, ",", true);
		System.out.println(builder.toString());
	}
}
