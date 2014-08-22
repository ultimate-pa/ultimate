package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * 
 * @author dietsch
 *
 * @param <T>
 */
public class SimpleCsvProvider<T> implements ICsvProvider<T> {

	private String[] mColumnTitles;
	private LinkedHashMap<String, T[]> mTable;

	public SimpleCsvProvider(String[] columnTitles, LinkedHashMap<String, T[]> table) {
		if (columnTitles == null) {
			throw new IllegalArgumentException("columnTitles is null");
		}
		if (table == null) {
			throw new IllegalArgumentException("table is null");
		}
		mColumnTitles = columnTitles;
		mTable = table;
	}

	public SimpleCsvProvider(String[] columnTitles) {
		this(columnTitles, new LinkedHashMap<String, T[]>());
	}

	@Override
	public String[] getColumnTitles() {
		return mColumnTitles;
	}

	@Override
	public Map<String, T[]> getTable() {
		return new LinkedHashMap<>(mTable);
	}

	@Override
	public String[] getRowTitles() {
		return mTable.keySet().toArray(new String[getTable().size()]);
	}

	@Override
	public void addRow(String rowName, T[] values) {
		if (values == null || values.length != getColumnTitles().length) {
			throw new IllegalArgumentException(
					"values are invalid (either null or not the same length as the number of columns of this CsvProvider");
		}
		mTable.put(rowName, values);
	}

	@Override
	public T[] getRow(String rowName) {
		return mTable.get(rowName);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String separator = ",";
		String lineSeparator = System.getProperty("line.separator");

		// get longest string
		int maxLength = 0;
		for (Entry<String, T[]> x : mTable.entrySet()) {
			if (x.getKey().length() > maxLength) {
				maxLength = x.getKey().length();
			}
		}
		for (int i = 0; i < maxLength + 1; i++) {
			sb.append(" ");
		}

		for (String s : mColumnTitles) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - 2, sb.length(), "").append(lineSeparator);

		for (Entry<String, T[]> x : mTable.entrySet()) {
			String rowTitle = x.getKey();
			checkForSeparators(rowTitle, separator, lineSeparator);
			sb.append(rowTitle).append(separator);
			for (int i = 0; i < maxLength + 1 - rowTitle.length(); i++) {
				sb.append(" ");
			}
			sb.append(rowTitle).append(separator);
			for (T value : x.getValue()) {
				String cellString = String.valueOf(value);
				checkForSeparators(cellString, separator, lineSeparator);
				sb.append(cellString).append(", ");
			}
			sb.replace(sb.length() - 2, sb.length(), "").append(lineSeparator);
		}

		return sb.toString();
	}

	@Override
	public StringBuilder toCsv(String rowHeaderTitle) {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		String separator = ",";
		sb.append(rowHeaderTitle).append(separator);
		for (String s : mColumnTitles) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - separator.length(), sb.length(), "").append(lineSeparator);
		
		for (Entry<String, T[]> x : mTable.entrySet()) {
			String rowTitle = x.getKey();
			checkForSeparators(rowTitle, separator, lineSeparator);
			sb.append(rowTitle).append(separator);
			for (T value : x.getValue()) {
				String cellString = String.valueOf(value);
				checkForSeparators(cellString, separator, lineSeparator);
				sb.append(cellString).append(separator);
			}
			sb.replace(sb.length() - separator.length(), sb.length(), "").append(lineSeparator);
		}
		
		return sb;
	}
	
	private void checkForSeparators(String cellString, String cellSeparator, String lineSeparator) {
		if (cellString.contains(cellSeparator)) {
			throw new IllegalArgumentException("The following cell contains the character that is used to separate cells: ");
		}
		if (cellString.contains(lineSeparator)) {
			throw new IllegalArgumentException("The following cell contains the character that is used to separate lines: ");
		}
	}

	@Override
	public boolean isEmpty() {
		return mTable.isEmpty();
	}

}