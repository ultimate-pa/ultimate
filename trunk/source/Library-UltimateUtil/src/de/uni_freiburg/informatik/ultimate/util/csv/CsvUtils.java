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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CsvUtils {

	public interface IExplicitConverter<T, K> {
		public K convert(T something);
	}

	/**
	 * Just convert one provider to another
	 *
	 * @param provider
	 * @param converter
	 * @return
	 */
	public static <T extends ICsvProvider<?>, K extends ICsvProvider<?>> K convertComplete(final T provider,
			final IExplicitConverter<T, K> converter) {
		return converter.convert(provider);
	}

	/**
	 * Converts one CsvProvider to another with an explicit converter. The converter is called for each value in the
	 * provider. This is always type-safe.
	 *
	 * @param provider
	 * @return
	 */
	public static <T, K> ICsvProvider<K> convertPerValue(final ICsvProvider<T> provider,
			final IExplicitConverter<T, K> converter) {
		final ICsvProvider<K> rtr = new SimpleCsvProvider<>(provider.getColumnTitles());
		final List<String> rowTitles = provider.getRowHeaders();
		final List<List<T>> table = provider.getTable();

		for (int i = 0; i < table.size(); ++i) {
			final List<T> oldrow = table.get(i);
			final List<K> newrow = new ArrayList<>();

			for (final T oldentry : oldrow) {
				newrow.add(converter.convert(oldentry));
			}

			final String rowTitle = rowTitles.get(i);
			rtr.addRow(rowTitle, newrow);
		}
		return rtr;
	}

	/**
	 * Constructs the cross-product of row headers and column headers and returns a ICsvProvider that contains only one
	 * row but the cross product as column headers.
	 *
	 * The original column headers are on the front, i.e. for [A,B] as column headers and [C,D] as row headers (in that
	 * order), you get a new ICsvProvider with [AyC, AyD, ByC, ByD] as column header and [] as row header, where y ==
	 * headerSeparator.
	 *
	 * @param provider
	 * @param headerSeparator
	 * @return
	 */
	public static <T> ICsvProvider<T> flatten(final ICsvProvider<T> provider, final String headerSeparator) {
		final ArrayList<String> newHeader = new ArrayList<>();
		final ArrayList<T> newRow = new ArrayList<>();
		final List<List<T>> currentMap = provider.getTable();

		for (int i = 0; i < provider.getColumnTitles().size(); i++) {
			final String currentColumnHeader = provider.getColumnTitles().get(i);

			for (int j = 0; j < provider.getRowHeaders().size(); j++) {
				final String currentRowHeader = provider.getRowHeaders().get(j);
				newHeader.add(currentColumnHeader + headerSeparator + currentRowHeader);
				newRow.add(currentMap.get(j).get(i));
			}
		}
		final ICsvProvider<T> rtr = new SimpleCsvProvider<>(newHeader);
		rtr.addRow(newRow);
		return rtr;
	}

	/**
	 * Creates a new ICsvProvider that has only the columns in columnTitles in the order of the original ICsvProvider.
	 *
	 * @param provider
	 * @param newColumnTitles
	 * @return
	 */
	public static <T> ICsvProvider<T> projectColumn(final ICsvProvider<T> provider, final String columnTitle) {
		return projectColumn(provider, Collections.singleton(columnTitle));
	}

	/**
	 * Creates a new ICsvProvider that has only the columns in columnTitles in the order of the original ICsvProvider.
	 *
	 * @param provider
	 * @param newColumnTitles
	 * @return
	 */
	public static <T> ICsvProvider<T> projectColumn(final ICsvProvider<T> provider, final String[] columnsToKeep) {
		return projectColumn(provider, Arrays.asList(columnsToKeep));
	}

	/**
	 * Creates a new ICsvProvider that has only the columns in columnTitles in the order of the original ICsvProvider.
	 *
	 * @param provider
	 * @param newColumnTitles
	 * @return
	 */
	public static <T> ICsvProvider<T> projectColumn(final ICsvProvider<T> provider,
			final Collection<String> newColumnTitles) {
		final ICsvProvider<T> newProvider = new SimpleCsvProvider<>(new ArrayList<>(newColumnTitles));

		if (provider.isEmpty()) {
			return newProvider;
		}

		// build index list
		final List<Integer> indexList = new ArrayList<>();
		for (final String newColumnTitle : newColumnTitles) {
			int newIdx = -1;
			for (int i = 0; i < provider.getColumnTitles().size(); ++i) {
				final String oldColumnTitle = provider.getColumnTitles().get(i);
				if (oldColumnTitle.equals(newColumnTitle)) {
					newIdx = i;
					break;
				}
			}
			indexList.add(newIdx);
		}

		int rowIndex = 0;
		for (final String rowTitle : provider.getRowHeaders()) {
			final List<T> newRow = new ArrayList<>();
			for (final int cellIndex : indexList) {
				if (cellIndex == -1) {
					newRow.add(null);
				} else {
					newRow.add(provider.getRow(rowIndex).get(cellIndex));
				}
			}
			rowIndex++;
			newProvider.addRow(rowTitle, newRow);
		}
		return newProvider;
	}

	/**
	 * Adds a new column at position index with column values values.
	 *
	 * @param provider
	 * @param columnTitle
	 * @param values
	 * @return
	 */
	public static <T> ICsvProvider<T> addColumn(final ICsvProvider<T> provider, final String columnTitle,
			final int index, final List<T> values) {
		if (index < 0 || index > provider.getColumnTitles().size()) {
			throw new IllegalArgumentException();
		}
		final List<String> oldTitles = provider.getColumnTitles();
		final List<String> newTitles = new ArrayList<>();

		for (int i = 0, j = 0; i < oldTitles.size() + 1; ++i) {
			if (i == index) {
				newTitles.add(i, columnTitle);
			} else {
				newTitles.add(i, oldTitles.get(j));
				j++;
			}
		}

		final SimpleCsvProvider<T> newProvider = new SimpleCsvProvider<>(newTitles);

		int k = 0;

		for (final List<T> oldRow : provider.getTable()) {
			final List<T> newRow = new ArrayList<>();

			for (int i = 0, j = 0; i < newTitles.size(); ++i) {
				if (i == index) {
					newRow.add(i, values.get(k));
				} else {
					newRow.add(i, oldRow.get(j));
					j++;
				}
			}
			newProvider.addRow(provider.getRowHeaders().get(k), newRow);
			k++;
		}

		return newProvider;
	}

	/**
	 * Creates a new provider where column titles are row titles and row titles are column titles.
	 *
	 * @param provider
	 * @return
	 */
	public static <T> ICsvProvider<T> transpose(final ICsvProvider<T> provider) {
		if (provider == null || provider.isEmpty()) {
			throw new IllegalArgumentException("provider may not be null or empty");
		}

		final List<String> newColumnTitles = new ArrayList<>(provider.getRowHeaders());
		final ICsvProvider<T> rtr = new SimpleCsvProvider<>(newColumnTitles);

		final List<String> newRowTitles = new ArrayList<>(provider.getColumnTitles());

		int i = 0;
		for (final String newRowTitle : newRowTitles) {
			final List<T> newRow = new ArrayList<>();

			for (final List<T> oldRow : provider.getTable()) {
				newRow.add(oldRow.get(i));
			}

			rtr.addRow(newRowTitle, newRow);
			i++;
		}
		return rtr;
	}

	@SuppressWarnings("unchecked")
	public static ICsvProvider<Object> concatenateRowsUnchecked(final ICsvProvider<?> a, final ICsvProvider<?> b) {
		return concatenateRows((ICsvProvider<Object>) a, (ICsvProvider<Object>) b);
	}

	/**
	 * Creates a new ICsvProvider that contains the rows of providerA and then the rows of providerB.
	 *
	 * If the providers have different columns the missing columns are added and the missing cells are filled with null
	 * values.
	 *
	 * The case where providerA and providerB contain the same column titles in different order is unsupported and an
	 * Exception is thrown.
	 *
	 * @param providerA
	 * @param providerB
	 * @return
	 */
	public static <T> ICsvProvider<T> concatenateRows(final ICsvProvider<T> providerA,
			final ICsvProvider<T> providerB) {
		final List<String> providerAColumns = providerA.getColumnTitles();
		final List<String> providerBColumns = providerB.getColumnTitles();
		List<String> resultColumns;
		final List<Integer> additionalColumnForProviderA = new ArrayList<>();
		final List<Integer> additionalColumnForProviderB = new ArrayList<>();
		if (providerAColumns.isEmpty()) {
			resultColumns = providerBColumns;
		} else if (providerBColumns.isEmpty()) {
			resultColumns = providerBColumns;
		} else {
			resultColumns = new ArrayList<>();
			int pAindex = 0;
			int pBindex = 0;
			while (pAindex < providerAColumns.size() || pBindex < providerBColumns.size()) {
				String currentPACol = null;
				if (pAindex < providerAColumns.size()) {
					currentPACol = providerAColumns.get(pAindex);
				}
				String currentPBCol = null;
				if (pBindex < providerBColumns.size()) {
					currentPBCol = providerBColumns.get(pBindex);
				}

				if (currentPACol != null && currentPACol.equals(currentPBCol)) {
					resultColumns.add(currentPACol);
					pAindex++;
					pBindex++;
				} else if (pAindex < providerAColumns.size() && !providerBColumns.contains(currentPACol)) {
					if (pBindex < providerBColumns.size() && !providerAColumns.contains(currentPBCol)
							&& currentPBCol.compareTo(currentPACol) < 0) {
						// special case:
						// currentPACol does not occur in providerBColumns
						// currentPBCol does not occur in providerAColumns
						// hence we may add both next
						// Since currentPBCol precedes currentPACol in a lexicographic ordering,
						// we take currentPBCol
						resultColumns.add(currentPBCol);
						additionalColumnForProviderA.add(pAindex);
						pBindex++;
					} else {
						resultColumns.add(currentPACol);
						additionalColumnForProviderB.add(pBindex);
						pAindex++;
					}
				} else if (pBindex < providerBColumns.size() && !providerAColumns.contains(currentPBCol)) {
					resultColumns.add(currentPBCol);
					additionalColumnForProviderA.add(pAindex);
					pBindex++;
				} else {
					throw new IllegalArgumentException(
							"unable to merge, both providers have similar columns but in different order");
				}
			}
		}
		final ICsvProvider<T> result = new SimpleCsvProvider<>(resultColumns);
		int rowIndex = 0;
		for (final String rowTitle : providerA.getRowHeaders()) {
			final List<T> p1Row = providerA.getRow(rowIndex);
			result.addRow(rowTitle, insertNullElements(p1Row, additionalColumnForProviderA));
			++rowIndex;
		}
		rowIndex = 0;
		for (final String rowTitle : providerB.getRowHeaders()) {
			final List<T> p2Row = providerB.getRow(rowIndex);
			result.addRow(rowTitle, insertNullElements(p2Row, additionalColumnForProviderB));
			++rowIndex;
		}
		return result;
	}

	/**
	 * Creates a new ICsvProvider that contains the rows of all input CSV providers. The result is obtained by an
	 * iterative application of {@link #concatenateRows(ICsvProvider, ICsvProvider)}.
	 */
	public static <T, K extends ICsvProvider<T>> ICsvProvider<T> concatenateRows(final List<K> csvProviders) {
		ICsvProvider<T> result = new SimpleCsvProvider<>(new ArrayList<String>());
		for (final ICsvProvider<T> csvProvider : csvProviders) {
			result = concatenateRows(result, csvProvider);
		}
		return result;
	}

	/**
	 * Given a list of values and a list of (not strictly) ascending positive integers, return a list that has at each
	 * position that occurs in the integer list additionalNullValuePositions an additional cell whose value is null.
	 */
	private static <T> List<T> insertNullElements(final List<T> array,
			final List<Integer> additionalNullValuePositions) {
		final List<T> result = new LinkedList<>(array);
		for (int i = additionalNullValuePositions.size() - 1; i >= 0; i--) {
			result.add(additionalNullValuePositions.get(i), null);
		}
		return result;
	}

	/**
	 * Given a map, return an ICsvProvider that has a single row. Its column header are the keys of the map, the row
	 * entries are the values of the map.
	 */
	public static <T> ICsvProvider<T> constructCvsProviderFromMap(final Map<String, T> map) {
		final List<String> keys = new ArrayList<>(map.keySet());
		final SimpleCsvProvider<T> scp = new SimpleCsvProvider<>(keys);
		final List<T> values = new ArrayList<>();
		for (final String key : keys) {
			values.add(map.get(key));
		}
		scp.addRow(values);
		return scp;
	}

	public static <T> StringBuilder toHTML(final ICsvProvider<T> provider, StringBuilder currentBuilder,
			final boolean withHTMLHeaders, IExplicitConverter<T, String> cellDecorator) {
		if (currentBuilder == null) {
			currentBuilder = new StringBuilder();
		}

		if (cellDecorator == null) {
			cellDecorator = new IExplicitConverter<T, String>() {
				@Override
				public String convert(final T something) {
					if (something == null) {
						return "-";
					}
					return something.toString();
				}
			};
		}

		final String linebreak = System.getProperty("line.separator");

		if (withHTMLHeaders) {
			currentBuilder.append("<html><body>").append(linebreak);
		}
		currentBuilder.append("<table style=\"width:100%\">").append(linebreak);

		if (hasRowHeaders(provider)) {
			final List<String> columnHeaders = provider.getColumnTitles();
			currentBuilder.append("<tr><th></th>");
			for (final String header : columnHeaders) {
				currentBuilder.append("<th>").append(header).append("</th>");
			}
			currentBuilder.append("</tr>").append(linebreak);

			final List<String> rowHeaders = provider.getRowHeaders();
			final List<List<T>> rows = provider.getTable();
			for (int i = 0; i < rows.size(); ++i) {
				currentBuilder.append("<tr><td>");
				currentBuilder.append(rowHeaders.get(i));
				currentBuilder.append("</td>");
				for (final T cell : rows.get(i)) {
					currentBuilder.append("<td>").append(cellDecorator.convert(cell)).append("</td>");
				}
				currentBuilder.append("</tr>").append(linebreak);
			}

		} else {
			final List<String> columnHeaders = provider.getColumnTitles();
			currentBuilder.append("<tr>");
			for (final String header : columnHeaders) {
				currentBuilder.append("<th>").append(header).append("</th>");
			}
			currentBuilder.append("</tr>").append(linebreak);

			final List<List<T>> rows = provider.getTable();
			for (int i = 0; i < rows.size(); ++i) {
				currentBuilder.append("<tr>");
				for (final T cell : rows.get(i)) {
					currentBuilder.append("<td>").append(cellDecorator.convert(cell)).append("</td>");
				}
				currentBuilder.append("</tr>").append(linebreak);
			}
		}

		currentBuilder.append("</table>").append(linebreak);
		if (withHTMLHeaders) {
			currentBuilder.append("</body></html>").append(linebreak);
		}

		return currentBuilder;
	}

	private static <T> boolean hasRowHeaders(final ICsvProvider<T> provider) {
		final List<String> rowHeaders = provider.getRowHeaders();
		if (rowHeaders == null || rowHeaders.isEmpty()) {
			return false;
		}

		for (final String header : rowHeaders) {
			if (header != null && !header.isEmpty()) {
				return true;
			}
		}
		return false;
	}

}
