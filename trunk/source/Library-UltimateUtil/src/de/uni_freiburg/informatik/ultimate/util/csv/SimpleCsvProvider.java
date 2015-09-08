/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
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
			if (rowTitle == null) {
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
	public StringBuilder toCsv(StringBuilder sb, String cellSeparator) {
		if (sb == null) {
			sb = new StringBuilder();
		}

		String lineSeparator = System.getProperty("line.separator");
		String separator = ",";
		if (cellSeparator != null && !cellSeparator.isEmpty()) {
			separator = cellSeparator;
		}

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
				cellString = cellString.replace(lineSeparator, "").replace(separator, "");
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
					"The following cell contains the character that is used to separate cells: " + cellString);
		}
		if (cellString.contains(lineSeparator)) {
			throw new IllegalArgumentException(
					"The following cell contains the character that is used to separate lines: " + cellString);
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

	@Override
	public void renameColumnTitle(String oldName, String newName) {
		ArrayList<String> names = new ArrayList<>();
		for (String title : getColumnTitles()) {
			if (title.equals(oldName)) {
				names.add(newName);
			} else {
				names.add(title);
			}
		}
		mColumnTitles = names;
	}

}
