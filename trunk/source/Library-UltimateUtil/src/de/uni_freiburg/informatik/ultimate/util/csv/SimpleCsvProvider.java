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

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class SimpleCsvProvider<T> implements ICsvProvider<T> {
	private List<String> mColumnTitles;
	private final List<String> mRowTitles;
	private final List<List<T>> mTable;

	/**
	 * @param columnTitles
	 *            The column titles.
	 */
	public SimpleCsvProvider(final List<String> columnTitles) {
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
		final List<List<T>> rtr = new ArrayList<>();
		for (final List<T> x : mTable) {
			rtr.add(new ArrayList<>(x));
		}
		return rtr;
	}

	@Override
	public List<String> getRowHeaders() {
		return mRowTitles;
	}

	@Override
	public void addRow(final String rowName, final List<T> values) {
		if (values == null || values.size() != mColumnTitles.size()) {
			throw new IllegalArgumentException(
					"values are invalid (either null or not the same length as the number of columns of this CsvProvider");
		}
		mRowTitles.add(rowName);
		mTable.add(values);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String separator = ",";
		final String lineSeparator = System.getProperty("line.separator");

		// get longest string
		int maxLength = 0;
		for (final String rowTitle : mRowTitles) {
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

		for (final String s : mColumnTitles) {
			sb.append(s).append(separator);
		}
		if (sb.length() >= 2) {
			sb.replace(sb.length() - 2, sb.length(), "");
		}
		sb.append(lineSeparator);

		for (int i = 0; i < mTable.size(); ++i) {
			final List<T> row = mTable.get(i);
			String rowTitle = mRowTitles.get(i);

			if (rowTitle == null) {
				rowTitle = "";
			}

			checkForSeparators(rowTitle, separator, lineSeparator);
			sb.append(rowTitle);
			for (int j = 0; j < maxLength + 1 - rowTitle.length(); j++) {
				sb.append(" ");
			}
			for (final T value : row) {
				final String cellString = String.valueOf(value);
				checkForSeparators(cellString, separator, lineSeparator);
				sb.append(cellString).append(", ");
			}
			if (sb.length() >= 2) {
				sb.replace(sb.length() - 2, sb.length(), "");
			}
			sb.append(lineSeparator);
		}

		return sb.toString();
	}

	@Override
	public StringBuilder toCsv(StringBuilder sb, final String cellSeparator, final boolean printColHeader) {
		if (sb == null) {
			sb = new StringBuilder();
		}

		// only output an extra column for row headers if there is the need for it
		final boolean printRowHeaderColumn = hasRowHeaders();

		final String lineSeparator = System.getProperty("line.separator");
		String separator = ",";
		if (cellSeparator != null && !cellSeparator.isEmpty()) {
			separator = cellSeparator;
		}

		if (printRowHeaderColumn) {
			sb.append(separator);
		}
		if (printColHeader) {
			for (final String s : mColumnTitles) {
				if (s == null || s.isEmpty()) {
					sb.append("NOTITLE").append(separator);
				} else {
					checkForSeparators(s, separator, lineSeparator);
					sb.append(s).append(separator);
				}
			}

			if (sb.length() >= separator.length()) {
				sb.replace(sb.length() - separator.length(), sb.length(), "");
			}
			sb.append(lineSeparator);
		}
		for (int i = 0; i < mTable.size(); ++i) {
			final List<T> row = mTable.get(i);
			String rowTitle = mRowTitles.get(i);

			if (printRowHeaderColumn) {
				if (rowTitle == null) {
					rowTitle = "";
				}

				checkForSeparators(rowTitle, separator, lineSeparator);
				sb.append(rowTitle).append(separator);
			}
			for (final T value : row) {
				String cellString = String.valueOf(value);
				cellString = cellString.replace(lineSeparator, "").replace(separator, "");
				checkForSeparators(cellString, separator, lineSeparator);
				sb.append(cellString).append(separator);
			}
			if (sb.length() >= separator.length()) {
				sb.replace(sb.length() - separator.length(), sb.length(), "");
			}
			sb.append(lineSeparator);
		}

		return sb;
	}

	private static void checkForSeparators(final String cellString, final String cellSeparator,
			final String lineSeparator) {
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
	public void addRow(final List<T> values) {
		addRow(null, values);
	}

	@Override
	public List<T> getRow(final int index) {
		if (index < 0 || index >= mTable.size()) {
			return null;
		}
		return mTable.get(index);
	}

	@Override
	public void renameColumnTitle(final String oldName, final String newName) {
		final ArrayList<String> names = new ArrayList<>();
		for (final String title : getColumnTitles()) {
			if (title.equals(oldName)) {
				names.add(newName);
			} else {
				names.add(title);
			}
		}
		mColumnTitles = names;
	}

	/**
	 * @return {@code true} iff there is at least one non-null row header.
	 */
	private boolean hasRowHeaders() {
		for (final String rowTitle : mRowTitles) {
			if (rowTitle != null) {
				return true;
			}
		}
		return false;
	}

	@Override
	public int getRowCount() {
		return mTable.size();
	}

	public static SimpleCsvProvider<Object> constructCsvProviderReflectively(final Object instance) {
		if (instance == null) {
			throw new IllegalArgumentException("instance is null");
		}

		// collect all values
		final List<String> columnTitles = new ArrayList<>();
		final List<Object> values = new ArrayList<>();
		for (final Field field : instance.getClass().getDeclaredFields()) {
			if (field.isAnnotationPresent(CsvColumn.class)) {
				try {
					final Object value = field.get(instance);
					final CsvColumn annot = field.getAnnotation(CsvColumn.class);
					final String name = annot.value();
					columnTitles.add(name);
					values.add(value);
				} catch (final IllegalArgumentException e) {
					throw new RuntimeException(e);
				} catch (final IllegalAccessException e) {
					throw new RuntimeException(e);
				}
			}
		}

		if (values.isEmpty()) {
			return new SimpleCsvProvider<>(Collections.emptyList());
		}

		final SimpleCsvProvider<Object> csvProvider = new SimpleCsvProvider<>(columnTitles);
		csvProvider.addRow(values);
		return csvProvider;
	}

	/**
	 * Annotation with which you mark a field as column provider in some object
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@Target(value = { ElementType.METHOD, ElementType.FIELD })
	@Retention(RetentionPolicy.RUNTIME)
	public @interface CsvColumn {
		String value();
	}
}
