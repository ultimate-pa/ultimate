package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch
 * 
 * @param <T>
 */
public class SimpleCsvProvider<T> implements ICsvProvider<T> {

	private List<String> mColumnTitles;
	private List<String> mRowTitles;
	private List<List<T>> mTable;

	public SimpleCsvProvider(List<String> columnTitles) {
		mColumnTitles = columnTitles;
		mTable = new ArrayList<>();
		mRowTitles = new ArrayList<>();
	}

	@Override
	public List<String> getColumnTitles() {
		return mColumnTitles;
	}

	@Override
	public List<List<T>> getTable() {
		List<List<T>> rtr = new ArrayList<>();
		for (List<T> x : mTable) {
			rtr.add(new ArrayList<>(x));
		}
		return rtr;
	}

	@Override
	public List<String> getRowHeaders() {
		return mRowTitles;
	}

	@Override
	public void addRow(String rowName, List<T> values) {
		if (values == null || values.size() != mColumnTitles.size()) {
			throw new IllegalArgumentException(
					"values are invalid (either null or not the same length as the number of columns of this CsvProvider");
		}
		mRowTitles.add(rowName);
		mTable.add(values);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String separator = ",";
		String lineSeparator = System.getProperty("line.separator");

		// get longest string
		int maxLength = 0;
		for (String rowTitle : mRowTitles) {
			if(rowTitle == null){
				continue;
			}
			if (rowTitle.length() > maxLength) {
				maxLength = rowTitle.length();
			}
		}
		for (int i = 0; i < maxLength + 1; i++) {
			sb.append(" ");
		}

		for (String s : mColumnTitles) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - 2, sb.length(), "").append(lineSeparator);

		for (int i = 0; i < mTable.size(); ++i) {
			List<T> row = mTable.get(i);
			String rowTitle = mRowTitles.get(i);

			if (rowTitle == null) {
				rowTitle = "";
			}

			checkForSeparators(rowTitle, separator, lineSeparator);
			sb.append(rowTitle).append(separator);
			for (int j = 0; j < maxLength + 1 - rowTitle.length(); j++) {
				sb.append(" ");
			}
			sb.append(rowTitle).append(separator);
			for (T value : row) {
				String cellString = String.valueOf(value);
				checkForSeparators(cellString, separator, lineSeparator);
				sb.append(cellString).append(", ");
			}
			sb.replace(sb.length() - 2, sb.length(), "").append(lineSeparator);
		}

		return sb.toString();
	}

	@Override
	public StringBuilder toCsv() {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		String separator = ",";
		sb.append(separator);
		for (String s : mColumnTitles) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - separator.length(), sb.length(), "").append(lineSeparator);

		for (int i = 0; i < mTable.size(); ++i) {
			List<T> row = mTable.get(i);
			String rowTitle = mRowTitles.get(i);

			if (rowTitle == null) {
				rowTitle = "";
			}

			checkForSeparators(rowTitle, separator, lineSeparator);
			sb.append(rowTitle).append(separator);
			for (T value : row) {
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
			throw new IllegalArgumentException(
					"The following cell contains the character that is used to separate cells: ");
		}
		if (cellString.contains(lineSeparator)) {
			throw new IllegalArgumentException(
					"The following cell contains the character that is used to separate lines: ");
		}
	}

	@Override
	public boolean isEmpty() {
		return mTable.isEmpty();
	}

	@Override
	public void addRow(List<T> values) {
		addRow(null, values);
	}

	@Override
	public List<T> getRow(int index) {
		if (index < 0 || index >= mTable.size()) {
			return null;
		}
		return mTable.get(index);
	}


}