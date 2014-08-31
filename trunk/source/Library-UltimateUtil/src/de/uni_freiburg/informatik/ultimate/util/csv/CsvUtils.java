package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * 
 * @author dietsch
 * 
 */
public class CsvUtils {

	public interface IExplicitConverter<T, K> {
		public K convert(T something);
	}

	/**
	 * Converts one CsvProvider to another with an explicit converter. This is
	 * always type-safe.
	 * 
	 * @param provider
	 * @return
	 */
	public static <T, K> ICsvProvider<K> convert(ICsvProvider<T> provider, IExplicitConverter<T, K> converter) {
		ICsvProvider<K> rtr = new SimpleCsvProvider<>(provider.getColumnTitles());
		List<String> rowTitles = provider.getRowHeaders();
		List<List<T>> table = provider.getTable();

		for (int i = 0; i < table.size(); ++i) {
			List<T> oldrow = table.get(i);
			List<K> newrow = new ArrayList<>();

			for (T oldentry : oldrow) {
				newrow.add(converter.convert(oldentry));
			}

			String rowTitle = rowTitles.get(i);
			rtr.addRow(rowTitle, newrow);
		}
		return rtr;
	}

	/**
	 * Constructs the cross-product of row headers and column headers and
	 * returns a ICsvProvider that contains only one row but the cross product
	 * as column headers.
	 * 
	 * The original column headers are on the front, i.e. for [A,B] as column
	 * headers and [C,D] as row headers (in that order), you get a new
	 * ICsvProvider with [AyC, AyD, ByC, ByD] as column header and [] as row
	 * header, where y == headerSeparator.
	 * 
	 * @param provider
	 * @param headerSeparator
	 * @return
	 */
	public static <T> ICsvProvider<T> flatten(ICsvProvider<T> provider, String headerSeparator) {
		ArrayList<String> newHeader = new ArrayList<>();
		ArrayList<T> newRow = new ArrayList<>();
		List<List<T>> currentMap = provider.getTable();

		for (int i = 0; i < provider.getColumnTitles().size(); i++) {
			String currentColumnHeader = provider.getColumnTitles().get(i);

			for (int j = 0; j < provider.getRowHeaders().size(); j++) {
				String currentRowHeader = provider.getRowHeaders().get(j);
				newHeader.add(currentColumnHeader + headerSeparator + currentRowHeader);
				newRow.add(currentMap.get(j).get(i));
			}
		}
		ICsvProvider<T> rtr = new SimpleCsvProvider<>(newHeader);
		rtr.addRow(newRow);
		return rtr;
	}

	public static <T> ICsvProvider<T> projectColumn(ICsvProvider<T> provider, String columnTitle) {
		return projectColumn(provider, Collections.singleton(columnTitle));
	}

	/**
	 * Creates a new ICsvProvider that has only the columns in columnTitles in
	 * the order of the original ICsvProvider.
	 * 
	 * @param provider
	 * @param newColumnTitles
	 * @return
	 */
	public static <T> ICsvProvider<T> projectColumn(ICsvProvider<T> provider, Collection<String> newColumnTitles) {
		ICsvProvider<T> newProvider = new SimpleCsvProvider<>(new ArrayList<>(newColumnTitles));

		if (provider.isEmpty()) {
			return newProvider;
		}

		int rowIndex = 0;
		for (String rowTitle : provider.getRowHeaders()) {
			List<T> newRow = new ArrayList<>();
			int i = 0;
			int j = 0;
			for (String originalColumnTitle : provider.getColumnTitles()) {
				if (newColumnTitles.contains(originalColumnTitle)) {
					newRow.add(i, provider.getRow(rowIndex).get(j));
					i++;
				}
				j++;
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
	public static <T> ICsvProvider<T> addColumn(ICsvProvider<T> provider, String columnTitle, int index, List<T> values) {
		if (index < 0 || index > provider.getColumnTitles().size()) {
			throw new IllegalArgumentException();
		}
		List<String> oldTitles = provider.getColumnTitles();
		List<String> newTitles = new ArrayList<>();

		for (int i = 0, j = 0; i < oldTitles.size() + 1; ++i) {
			if (i == index) {
				newTitles.add(i, columnTitle);
			} else {
				newTitles.add(i, oldTitles.get(j));
				j++;
			}
		}

		SimpleCsvProvider<T> newProvider = new SimpleCsvProvider<>(newTitles);

		int k = 0;

		for (List<T> oldRow : provider.getTable()) {
			List<T> newRow = new ArrayList<>();

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
	 * Creates a new provider where column titles are row titles and row titles
	 * are column titles.
	 * 
	 * @param provider
	 * @return
	 */
	public static <T> ICsvProvider<T> transpose(ICsvProvider<T> provider) {
		if (provider == null || provider.isEmpty()) {
			throw new IllegalArgumentException("provider may not be null or empty");
		}

		List<String> newColumnTitles = new ArrayList<>(provider.getRowHeaders());
		ICsvProvider<T> rtr = new SimpleCsvProvider<>(newColumnTitles);

		List<String> newRowTitles = new ArrayList<>(provider.getColumnTitles());

		int i = 0;
		for (String newRowTitle : newRowTitles) {
			List<T> newRow = new ArrayList<T>();

			for (List<T> oldRow : provider.getTable()) {
				newRow.add(oldRow.get(i));
			}

			rtr.addRow(newRowTitle, newRow);
			i++;
		}
		return rtr;
	}

	/**
	 * Creates a new ICsvProvider that contains the rows of providerA and then
	 * the rows of providerB.
	 * 
	 * If the providers have different columns the missing columns are added and
	 * the missing cells are filled with null values.
	 * 
	 * The case where providerA and providerB contain the same column titles in
	 * different order is unsupported and an Exception is thrown.
	 * 
	 * @param providerA
	 * @param providerB
	 * @return
	 */
	public static <T> ICsvProvider<T> concatenateRows(ICsvProvider<T> providerA, ICsvProvider<T> providerB) {
		List<String> providerAColumns = providerA.getColumnTitles();
		List<String> providerBColumns = providerB.getColumnTitles();
		List<String> resultColumns;
		List<Integer> additionalColumnForProviderA = new ArrayList<Integer>();
		List<Integer> additionalColumnForProviderB = new ArrayList<Integer>();
		if (providerAColumns.size() == 0) {
			resultColumns = providerBColumns;
		} else if (providerBColumns.size() == 0) {
			resultColumns = providerBColumns;
		} else {
			resultColumns = new ArrayList<String>();
			int pAindex = 0;
			int pBindex = 0;
			while (pAindex < providerAColumns.size() || pBindex < providerBColumns.size()) {
				String currentPACol = providerAColumns.get(pAindex);
				String currentPBCol = providerBColumns.get(pBindex);
				if (currentPACol.equals(currentPBCol)) {
					resultColumns.add(currentPACol);
					pAindex++;
					pBindex++;
				} else if (pAindex < providerAColumns.size() && !providerBColumns.contains(currentPACol)) {
					resultColumns.add(currentPACol);
					additionalColumnForProviderB.add(pBindex);
					pAindex++;
				} else if (pBindex < providerBColumns.size() && !providerAColumns.contains(currentPBCol)) {
					resultColumns.add(currentPBCol);
					additionalColumnForProviderA.add(pAindex);
					pBindex++;
				} else {
					throw new IllegalArgumentException("unable to merge, both "
							+ "providers have similar columns but in different order");
				}
			}
		}
		ICsvProvider<T> result = new SimpleCsvProvider<>(resultColumns);
		int rowIndex = 0;
		for (String rowTitle : providerA.getRowHeaders()) {
			List<T> p1Row = providerA.getRow(rowIndex);
			result.addRow(rowTitle, insertNullElements(p1Row, additionalColumnForProviderA));
			++rowIndex;
		}
		rowIndex = 0;
		for (String rowTitle : providerB.getRowHeaders()) {
			List<T> p2Row = providerB.getRow(rowIndex);
			result.addRow(rowTitle, insertNullElements(p2Row, additionalColumnForProviderB));
			++rowIndex;
		}
		return result;
	}

	/**
	 * Given a list of values and a list of (not strictly) ascending positive
	 * integers, return a list that has at each position that occurs in the
	 * integer list additionalNullValuePositions an additional cell whose value
	 * is null.
	 */
	private static <T> List<T> insertNullElements(List<T> array, List<Integer> additionalNullValuePositions) {
		List<T> result = new LinkedList<T>(array);
		for (int i = additionalNullValuePositions.size() - 1; i >= 0; i--) {
			result.add(additionalNullValuePositions.get(i), null);
		}
		return result;
	}
	
	/**
	 * Given a map, return an ICsvProvider that has a single row. Its column
	 * header are the keys of the map, the row entries are the values of the 
	 * map.
	 */
	public static <T> ICsvProvider<T> constructCvsProviderFromMap(Map<String,T> map) {
		List<String> keys = new ArrayList<String>(map.keySet());
		SimpleCsvProvider<T> scp = new SimpleCsvProvider<T>(keys);
		List<T> values = new ArrayList<T>();
		for (String key : keys) {
			values.add(map.get(key));
		}
		scp.addRow(values);
		return scp;
	}

}
