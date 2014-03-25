package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
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
		return new SimpleCsvProvider<>(provider.getColumnTitle(), newMap);
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

		for (int i = 0; i < provider.getColumnTitle().length; i++) {
			String currentColumnHeader = provider.getColumnTitle()[i];
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
		throw new UnsupportedOperationException();
	}

	public static <T> ICsvProvider<T> projectColumn(ICsvProvider<T> provider, Collection<String> columnTitles) {
		throw new UnsupportedOperationException();
	}

}
