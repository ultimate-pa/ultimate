/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Creates a summary table in the HTML-format from a given data table in the
 * CSV-format. Empty lines and data entries equals to {@link CSV_ENTRY_NO_VALUE}
 * will get highlighted.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 */
public final class CsvToHtmlSummary {

	/**
	 * If an data entry of the CSV-content is equals to this constant, then the
	 * HTML table will highlight the entry.
	 */
	public static final String CSV_ENTRY_NO_VALUE = "null";
	/**
	 * Separator to use for dividing the content in a CSV-formatted text.
	 */
	private static final String CSV_SEPARATOR = ",";
	/**
	 * Html text to use between head and content.
	 */
	private static final String HTML_HEAD_TO_CONTENT = "</head><body>";
	/**
	 * Placeholder for representing no value in a HTML formatted table.
	 */
	private static final String HTML_NO_VALUE = "&ndash;";
	/**
	 * Html text to use at the beginning of the html file.
	 */
	private static final String HTML_PRE = "<!DOCTYPE html><html><head>";
	/**
	 * Html text to use at the end of the html file.
	 */
	private static final String HTML_SUCC = "</body></html>";
	/**
	 * Html tag for table cells.
	 */
	private static final String HTML_TABLE_CELL_TAG = "td";
	/**
	 * Html tag for table headers.
	 */
	private static final String HTML_TABLE_HEADER_TAG = "th";
	/**
	 * Html tag for table rows.
	 */
	private static final String HTML_TABLE_ROW_TAG = "tr";

	/**
	 * Converts content given by rows in a CSV-format into a summary table
	 * formatted in HTML.
	 * 
	 * @param csvFileRows
	 *            Content to convert given by rows in a CSV-format
	 * @return The converted content as summary table formatted in HTML
	 */
	public static String convertCsvByRowsToHtmlSummary(final Iterable<String> csvFileRows) {
		final StringBuilder htmlText = new StringBuilder();
		final String lineSeparator = CoreUtil.getPlatformLineSeparator();

		htmlText.append(HTML_PRE);
		htmlText.append("<title>HTML Summary</title>");

		// TODO Store the JS-File somewhere more appropriate. (You may download
		// the file and include it in ULTIMATE, together with the
		// ULTIMATE-license).
		// Java-Script
		htmlText.append(
				"<script type=\"text/javascript\" src=\"https://ajax.googleapis.com/ajax/libs/jquery/3.1.0/jquery.min.js\"></script>");
		htmlText.append("<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/sorttable.js\"></script>");
		htmlText.append("<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/markRows.js\"></script>");

		// TODO Store the CSS as file and somewhere more appropriate.
		// CSS
		htmlText.append("<style>");
		// Wikitable classes
		htmlText.append("table.wikitable { margin: 1em 0; background-color: #f9f9f9;"
				+ " border: 1px solid #aaa;border-collapse: collapse; color: black }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > tr > td,"
				+ " table.wikitable > * > tr > th, table.wikitable > * > tr > td {"
				+ " border: 1px solid #aaa; padding: 0.2em 0.4em }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > * > tr > th {"
				+ " background-color: #f2f2f2; text-align: center }");
		htmlText.append("table.wikitable > caption { font-weight: bold }");
		// Alternating row coloring
		htmlText.append("tr:nth-child(even) { background-color: #f9f9f9 }");
		htmlText.append("tr:nth-child(odd) { background-color: #e9e9e9 }");
		// Empty row highlighting
		htmlText.append(".emptyrow { background-color: #c9c9c9 !important; }");
		// Sortable icons
		htmlText.append("table.sortable th:not(.sorttable_sorted):not(.sorttable_sorted_reverse)"
				+ ":not(.sorttable_nosort):after { content: \" \\25B4\\25BE\"; }");
		// Mark rows
		htmlText.append("#markRowText { margin-left: 1em; }");
		htmlText.append(".markedRow { background-color: #FFB0B0 !important; }");
		htmlText.append("</style>");

		htmlText.append(HTML_HEAD_TO_CONTENT);
		final String htmlOpeningSymbol = "<";
		final String htmlClosingSymbol = ">";
		final String htmlClosingOpeningSymbol = "</";
		htmlText.append(
				"<span class=\"markedRow demoText\">Mark rows:</span><input type=\"text\" id=\"markRowText\" name=\"markRowText\" oninput=\"markRows()\" /><br/>");
		htmlText.append("<table id=\"contentTable\" class=\"wikitable sortable\">");

		boolean isFirstRow = true;
		for (final String row : csvFileRows) {
			// First row is header
			String cellTag = HTML_TABLE_CELL_TAG;
			if (isFirstRow) {
				cellTag = HTML_TABLE_HEADER_TAG;
			}

			// Empty row
			if (row.isEmpty()) {
				htmlText.append("<tr class=\"emptyrow\"><td colspan=\"100%\">&nbsp;</td></tr>" + lineSeparator);
				continue;
			}

			// Row is not empty
			final String[] cells = row.split(CSV_SEPARATOR);
			if (cells.length > 0) {
				htmlText.append(htmlOpeningSymbol + HTML_TABLE_ROW_TAG + htmlClosingSymbol);
				for (final String value : cells) {
					String valueText = value;
					if (value.equals(CSV_ENTRY_NO_VALUE)) {
						valueText = HTML_NO_VALUE;
					}
					htmlText.append(htmlOpeningSymbol + cellTag + htmlClosingSymbol + valueText
							+ htmlClosingOpeningSymbol + cellTag + htmlClosingSymbol);
				}
				htmlText.append(htmlClosingOpeningSymbol + HTML_TABLE_ROW_TAG + htmlClosingSymbol + lineSeparator);
			}

			isFirstRow = false;
		}

		htmlText.append("</table>");
		htmlText.append(HTML_SUCC);

		return htmlText.toString();
	}

	/**
	 * Demonstrates the usage of this class.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public static void main(final String[] args) throws IOException {
		final File desktop = new File(System.getProperty("user.home"), "Desktop");
		final File summaryPath = new File(desktop, "summary");

		// Iterate every CSV-File and generate the tables
		final FileFilter csvFilter = new FileFilter() {
			/*
			 * (non-Javadoc)
			 * 
			 * @see java.io.FileFilter#accept(java.io.File)
			 */
			@Override
			public boolean accept(final File file) {
				return file.getName().endsWith(".csv");
			}
		};
		for (final File csvFile : summaryPath.listFiles(csvFilter)) {
			// Generate HTML-Summary
			final CsvToHtmlSummary csvToHtmlSummary = new CsvToHtmlSummary(csvFile);

			// Write HTML-Summary to file
			PrintWriter writer = null;
			final File summaryFile = new File(summaryPath, csvFile.getName() + ".html");
			try {
				writer = new PrintWriter(new BufferedWriter(new FileWriter(summaryFile)));
				writer.print(csvToHtmlSummary.getHtmlSummary());
			} catch (final IOException e) {
				e.printStackTrace();
			} finally {
				if (writer != null) {
					writer.close();
				}
			}
		}
	}

	/**
	 * Reads a given file by rows and returns it row-wise.
	 * 
	 * @param file
	 *            File to read
	 * @return The given file row-wise iterable.
	 * @throws FileNotFoundException
	 *             If the given file could not be found.
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	private static Iterable<String> readFileByRows(final File file) throws IOException {
		final LinkedList<String> result = new LinkedList<>();
		final BufferedReader br = new BufferedReader(new FileReader(file));

		try {
			while (br.ready()) {
				String line = br.readLine();
				if (line == null) {
					break;
				}
				result.add(line);
			}
		} finally {
			br.close();
		}

		return result;
	}

	/**
	 * Splits the given text row-wise using the given line separator.
	 * 
	 * @param text
	 *            The text to split
	 * @param lineSeparatorRegex
	 *            The line separator which gets interpreted as Regex.
	 * @return The given text row-wise iterable.
	 */
	private static Iterable<String> splitTextByRows(final String text, final String lineSeparatorRegex) {
		final LinkedList<String> result = new LinkedList<>();
		// Implementing a manual split for maximal compatibility and efficiency
		// Pattern is: Anything (capturing) and then the separator
		Pattern pattern = Pattern.compile("(.*)" + lineSeparatorRegex);
		Matcher matcher = pattern.matcher(text);
		while (matcher.find()) {
			result.add(matcher.group(1));
		}
		return result;
	}

	/**
	 * The generated summary table formatted in HTML.
	 */
	private final String mHtmlSummary;

	/**
	 * Creates a new summary table representing the given content formatted in
	 * HTML.
	 * 
	 * @param csvFile
	 *            The file to create a table for formatted in CSV.
	 * @throws FileNotFoundException
	 *             If the given file could not be found.
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public CsvToHtmlSummary(final File csvFile) throws IOException {
		this(readFileByRows(csvFile));
	}

	/**
	 * Creates a new summary table representing the given content formatted in
	 * HTML.
	 * 
	 * @param csvFileRows
	 *            The content to create a table for formatted in CSV and
	 *            row-wise iterable
	 */
	public CsvToHtmlSummary(final Iterable<String> csvFileRows) {
		mHtmlSummary = convertCsvByRowsToHtmlSummary(csvFileRows);
		// TODO Adjust and embed this class to the existing summary system of
		// Ultimate.
	}

	/**
	 * Creates a new summary table representing the given content formatted in
	 * HTML.
	 * 
	 * @param csvFile
	 *            The content to create a table for formatted in CSV
	 */
	public CsvToHtmlSummary(final String csvFile) {
		this(csvFile, CoreUtil.getPlatformLineSeparator());
	}

	/**
	 * Creates a new summary table representing the given content formatted in
	 * HTML.
	 * 
	 * @param csvFile
	 *            The content to create a table for formatted in CSV
	 * @param lineSeparatorRegex
	 *            The line separator which gets interpreted as Regex.
	 */
	public CsvToHtmlSummary(final String csvFile, final String lineSeparatorRegex) {
		this(splitTextByRows(csvFile, lineSeparatorRegex));
	}

	/**
	 * Gets the generated summary table formatted in HTML.
	 * 
	 * @return The generated summary table formatted in HTML
	 */
	public String getHtmlSummary() {
		return mHtmlSummary;
	}
}
