package de.uni_freiburg.informatik.ultimate.util.csv;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

/**
 * 
 * @author dietsch
 * 
 */
public class CsvUtils {

	public interface IExplicitConverter<T, K> {
		public K convert(T something);

		public K[] createArray(int length);
	}

	/**
	 * Converts one CsvProvider to another with an explicit converter. This is
	 * always type-safe.
	 * 
	 * @param provider
	 * @return
	 */

	public static <T, K> ICsvProvider<K> convert(ICsvProvider<T> provider, IExplicitConverter<T, K> converter) {
		LinkedHashMap<String, K[]> newMap = new LinkedHashMap<>();
		for (Entry<String, T[]> entry : provider.getTable().entrySet()) {
			ArrayList<K> newArray = new ArrayList<>();
			for (T value : entry.getValue()) {
				newArray.add(converter.convert(value));
			}
			newMap.put(entry.getKey(), newArray.toArray((converter.createArray(newArray.size()))));
		}
		return new SimpleCsvProvider<>(provider.getColumnTitles(), newMap);
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
	 * @param buffer
	 *            A prototype array. Use an array of size 0 here.
	 * @return
	 */
	public static <T> ICsvProvider<T> flatten(ICsvProvider<T> provider, String headerSeparator, T[] buffer) {
		assert buffer != null && buffer.length == 0;
		ArrayList<String> newHeader = new ArrayList<>();
		ArrayList<T> newRow = new ArrayList<>();
		Map<String, T[]> currentMap = provider.getTable();

		for (int i = 0; i < provider.getColumnTitles().length; i++) {
			String currentColumnHeader = provider.getColumnTitles()[i];
			for (String currentRowHeader : currentMap.keySet()) {
				newHeader.add(currentColumnHeader + headerSeparator + currentRowHeader);
				newRow.add(currentMap.get(currentRowHeader)[i]);
			}
		}
		LinkedHashMap<String, T[]> newMap = new LinkedHashMap<>();
		newMap.put("", newRow.toArray(buffer));
		return new SimpleCsvProvider<>(newHeader.toArray(new String[0]), newMap);
	}

	public static <T> ICsvProvider<T> projectColumn(ICsvProvider<T> provider, String columnTitle) {
		return projectColumn(provider, Collections.singleton(columnTitle));
	}

	/**
	 * Creates a new ICsvProvider that has only the columns in columnTitles in
	 * the order of the original ICsvProvider.
	 * 
	 * @param provider
	 * @param columnTitles
	 * @return
	 */
	public static <T> ICsvProvider<T> projectColumn(ICsvProvider<T> provider, Collection<String> columnTitles) {
		SimpleCsvProvider<T> newProvider = new SimpleCsvProvider<>(columnTitles.toArray(new String[0]));

		if (provider.isEmpty()) {
			return newProvider;
		}

		T[] referenceType = provider.getRow(provider.getRowTitles()[0]);
		int newLength = columnTitles.size();

		for (String s : provider.getRowTitles()) {
			@SuppressWarnings("unchecked")
			T[] newvalues = (T[]) Array.newInstance(referenceType[0].getClass(), newLength);

			int i = 0;
			int j = 0;
			for (String k : provider.getColumnTitles()) {
				if (columnTitles.contains(k)) {
					newvalues[i] = provider.getRow(s)[j];
					i++;
				}
				j++;
			}
			newProvider.addRow(s, newvalues);
		}
		return newProvider;
	}

	/**
	 * Creates a new ICsvProvider that contains the rows of providerA and then
	 * the rows of providerB.
	 * 
	 * If the providers have the same number of column titles, the titles of
	 * providerA are used. If the length differs, an exception is thrown.
	 * 
	 * @param providerA
	 * @param providerB
	 * @return
	 */
	public static <T> ICsvProvider<T> concatenateRows(ICsvProvider<T> providerA, ICsvProvider<T> providerB) {

		String[] aTitles = providerA.getColumnTitles();
		if (aTitles.length != providerB.getColumnTitles().length) {
			throw new IllegalArgumentException();
		}

		SimpleCsvProvider<T> newProvider = new SimpleCsvProvider<>(aTitles);

		for (String rowName : providerA.getRowTitles()) {
			newProvider.addRow(rowName, providerA.getRow(rowName));
		}
		for (String rowName : providerB.getRowTitles()) {
			newProvider.addRow(rowName, providerB.getRow(rowName));
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
	public static <T> ICsvProvider<T> addColumn(ICsvProvider<T> provider, String columnTitle, int index, T[] values) {
		if (index < 0 || index > provider.getColumnTitles().length) {
			throw new IllegalArgumentException();
		}
		String[] oldTitles = provider.getColumnTitles();
		String[] newTitles = new String[oldTitles.length + 1];

		for (int i = 0, j = 0; i < newTitles.length; ++i) {
			if (i == index) {
				newTitles[i] = columnTitle;
			} else {
				newTitles[i] = oldTitles[j];
				j++;
			}
		}

		SimpleCsvProvider<T> newProvider = new SimpleCsvProvider<>(newTitles);

		int k = 0;
		for (String s : provider.getRowTitles()) {
			T[] rowValues = provider.getRow(s);
			@SuppressWarnings("unchecked")
			T[] newvalues = (T[]) Array.newInstance(rowValues[0].getClass(), oldTitles.length + 1);

			for (int i = 0, j = 0; i < newTitles.length; ++i) {
				if (i == index) {
					newvalues[i] = values[k];
				} else {
					newvalues[i] = rowValues[j];
					j++;
				}
			}
			newProvider.addRow(s, newvalues);
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
	@SuppressWarnings("unchecked")
	public static <T> ICsvProvider<T> transpose(ICsvProvider<T> provider) {
		if (provider == null || provider.isEmpty()) {
			throw new IllegalArgumentException("provider may not be null or empty");
		}

		String[] newColumnTitles = provider.getRowTitles();
		String[] newRowTitles = provider.getColumnTitles();
		T[] referenceType = provider.getRow(newColumnTitles[0]);
		LinkedHashMap<String, T[]> newMap = new LinkedHashMap<>();

		for (String s : newRowTitles) {
			newMap.put(s, ((T[]) Array.newInstance(referenceType[0].getClass(), newColumnTitles.length)));
		}
		int i = 0;
		for(String oldRowName : newColumnTitles){
			T[] oldrow = provider.getRow(oldRowName);
			int j = 0;
			for(String newRowName : newRowTitles){
				newMap.get(newRowName)[i] = oldrow[j];
				j++;
			}
			i++;
		}
		return new SimpleCsvProvider<>(newColumnTitles, newMap);
	}
	
	/**
	 * Creates a new ICsvProvider that contains the rows of providerA and then
	 * the rows of providerB.
	 * 
	 * If the providers have different columns the missing columns are added
	 * and the missing cells are filled with null values.
	 * 
	 * The case where providerA and providerB contain the same column titles
	 * in different order is unsupported and an Exception is thrown.
	 * 
	 * @param providerA
	 * @param providerB
	 * @return
	 */
	public static <T> ICsvProvider<T> concatenateRowsWithDifferentColumns(
			ICsvProvider<T> providerA, ICsvProvider<T> providerB) {
		List<String> providerAColumns = Arrays.asList(providerA.getColumnTitles());
		List<String> providerBColumns = Arrays.asList(providerB.getColumnTitles());
		List<Integer> additionalColumnForProviderA = new ArrayList<Integer>();
		List<Integer> additionalColumnForProviderB = new ArrayList<Integer>();
		List<String> resultColumns = new ArrayList<String>();
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
		SimpleCsvProvider<T> result = new SimpleCsvProvider<>(resultColumns.toArray(new String[resultColumns.size()]));
		for (String rowTitle : providerA.getRowTitles()) {
			T[] p1Row = providerA.getRow(rowTitle);
			result.addRow(rowTitle, insertNullElements(p1Row, additionalColumnForProviderA));
		}
		for (String rowTitle : providerB.getRowTitles()) {
			T[] p2Row = providerB.getRow(rowTitle);
			result.addRow(rowTitle, insertNullElements(p2Row, additionalColumnForProviderB));
		}
		return result;
	}
	
	/**
	 * Given an array and a list of (not strictly) ascending positive integers,
	 * return an array that has at each position that occurs in the list
	 * additionalNullValuePositions an additional cell whose value is null.
	 */
	@SuppressWarnings("unchecked")
	private static <T> T[] insertNullElements(T[] array, 
			List<Integer> additionalNullValuePositions) {
		List<T> result = new LinkedList<T>(Arrays.asList(array));
		for (int i=additionalNullValuePositions.size()-1; i>=0; i--) {
			result.add(additionalNullValuePositions.get(i), null);
		}
		return (T[]) result.toArray();
	}
	
}
