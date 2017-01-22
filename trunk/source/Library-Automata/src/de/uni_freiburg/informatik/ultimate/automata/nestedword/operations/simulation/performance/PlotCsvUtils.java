package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

/**
 * Provides utility methods for CSV files used for plotting performance entry
 * tables.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 */
public final class PlotCsvUtils {
	/**
	 * Character representing the separator used in CSV files.
	 */
	public static final String CSV_SEPARATOR = "\t";
	/**
	 * File representing the users Desktop.
	 */
	public static final File DESKTOP = new File(System.getProperty("user.home"), "Desktop");

	/**
	 * Appends the given column content to the given CSV file.
	 * 
	 * @param csvFile
	 *            CSV file to add the column to
	 * @param columnContent
	 *            Column to add
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void appendColumnToCsv(final File csvFile, final List<String> columnContent) throws IOException {
		final List<String> fileContent = getFileContent(csvFile);

		if (fileContent.size() != columnContent.size()) {
			System.err.println("Error: Size of CSV must be equal to the size of the column to add.");
		}

		final Iterator<String> csvIter = fileContent.iterator();
		final Iterator<String> columnIter = columnContent.iterator();

		final List<String> nextContent = new LinkedList<String>();
		while (csvIter.hasNext()) {
			String csvLine = csvIter.next();
			final String columnLine = columnIter.next();

			csvLine += CSV_SEPARATOR + columnLine;

			nextContent.add(csvLine);
		}

		writeFile(csvFile, nextContent);
	}

	/**
	 * Gets the content of the column given by its index.
	 * 
	 * @param rawData
	 *            The data of the CSV file
	 * @param index
	 *            The index of the column to get
	 * @return The content of the column to get
	 */
	public static List<String> getColumnContent(final List<String> rawData, final int index) {
		final List<String> entries = new LinkedList<>();

		for (final String row : rawData) {
			final String[] data = row.split(CSV_SEPARATOR);
			entries.add(data[index]);
		}

		return entries;
	}

	/**
	 * Gets the content of a file and returns it as list of lines.
	 * 
	 * @param file
	 *            Path to the file
	 * @return List of lines from the content
	 * @throws IOException
	 *             If an I/O-Exception occurs
	 */
	public static List<String> getFileContent(final File file) throws IOException {
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(file)));
		final List<String> content = new ArrayList<String>();

		String line = br.readLine();
		while (line != null) {
			content.add(line);
			line = br.readLine();
		}

		br.close();
		return content;
	}

	/**
	 * Merges the plotting results of two plot files.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void main(final String[] args) throws IOException {
		System.out.println("Starting...");

		// Column indices
		final int sizeOutputIndex = 14 - 1;
		final int overallTimeIndex = 15 - 1;
		final int appendedFirstIndex = 16 - 1;
		final int appendedSecondIndex = 17 - 1;

		// File names
		final File directFile = new File(DESKTOP, "plotData_direct.csv");
		final File delayedFile = new File(DESKTOP, "plotData_delayed.csv");
		final File combinedFile = new File(DESKTOP, "plotData_combined.csv");

		final List<String> directRawData = getFileContent(directFile);
		final List<String> delayedRawData = getFileContent(delayedFile);

		// Columns to add
		final List<String> delayedSizeOutputData = getColumnContent(delayedRawData, sizeOutputIndex);
		final List<String> delayedOverallTimeData = getColumnContent(delayedRawData, overallTimeIndex);

		// Take the whole file
		writeFile(combinedFile, directRawData);
		renameColumnHeader(combinedFile, sizeOutputIndex, "SIZE_OUTPUT_DIRECT");
		renameColumnHeader(combinedFile, overallTimeIndex, "OVERALL_TIME_DIRECT");
		// Add other columns
		appendColumnToCsv(combinedFile, delayedSizeOutputData);
		appendColumnToCsv(combinedFile, delayedOverallTimeData);
		renameColumnHeader(combinedFile, appendedFirstIndex, "SIZE_OUTPUT_DELAYED");
		renameColumnHeader(combinedFile, appendedSecondIndex, "OVERALL_TIME_DELAYED");

		System.out.println("Finished.");
	}

	/**
	 * Renames the header of the column given by its index.
	 * 
	 * @param csvFile
	 *            The CSV file to rename its column
	 * @param index
	 *            The index of the column to rename
	 * @param name
	 *            The new header name
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void renameColumnHeader(final File csvFile, final int index, final String name) throws IOException {
		final List<String> content = getFileContent(csvFile);
		final Iterator<String> lineIterator = content.iterator();

		final String headerLine = lineIterator.next();
		final String[] headers = headerLine.split(CSV_SEPARATOR);
		headers[index] = name;
		String nextHeaderLine = "";
		for (int i = 0; i < headers.length; i++) {
			nextHeaderLine += headers[i];

			if (i != headers.length - 1) {
				nextHeaderLine += CSV_SEPARATOR;
			}
		}

		final List<String> nextContent = new LinkedList<String>();
		nextContent.add(nextHeaderLine);

		while (lineIterator.hasNext()) {
			nextContent.add(lineIterator.next());
		}

		writeFile(csvFile, nextContent);
	}

	/**
	 * Writes the given file with the given content. Existing content will be
	 * overwritten.
	 * 
	 * @param file
	 *            The file to write to
	 * @param content
	 *            The content to write into the file
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void writeFile(final File file, final List<String> content) throws IOException {
		final PrintWriter pw = new PrintWriter(new FileWriter(file, false));

		for (final String line : content) {
			pw.println(line);
		}

		pw.close();
	}

	/**
	 * Utility class. No implementation.
	 */
	private PlotCsvUtils() {

	}
}
