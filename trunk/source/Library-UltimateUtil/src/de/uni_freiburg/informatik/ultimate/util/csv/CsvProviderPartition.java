/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Predicate;

/**
 * Encapsulates a collection of {@link ICsvProvider}s.
 * <p>
 * NOTE: Data contains shallow copies, i.e., modifications affect both the original data and this wrapper. Use the
 * {@link #copy()} method to avoid such problems.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderPartition<T> {
	private Collection<ICsvProvider<T>> mCsvs;
	
	/**
	 * Constructor from an existing CSV partition.
	 * 
	 * @param csvPartition
	 *            CSV partition
	 */
	public CsvProviderPartition(final Collection<ICsvProvider<T>> csvPartition) {
		mCsvs = csvPartition;
	}
	
	/**
	 * Constructor from an existing CSV where grouping is applied with respect to a given column. This means that all
	 * rows with the same entry in that column are in the same group.
	 * 
	 * @param csv
	 *            CSV provider
	 * @param column
	 *            aggregation column
	 */
	public CsvProviderPartition(final ICsvProvider<T> csv, final String column) {
		mCsvs = groupByColumnKeyAndThreshold(csv, column, null);
	}
	
	/**
	 * Constructor from an existing CSV where grouping is applied with respect to an integer split of one column.
	 * <p>
	 * This constructor only makes sense if the values in the respective row are numeric data.
	 * 
	 * @param csv
	 *            CSV provider
	 * @param column
	 *            aggregation column
	 * @param thresholds
	 *            threshold values for different bins
	 */
	public CsvProviderPartition(final ICsvProvider<T> csv, final String column, final int[] thresholds) {
		mCsvs = groupByColumnKeyAndThreshold(csv, column, thresholds);
	}
	
	public Iterable<ICsvProvider<T>> getCsvs() {
		return mCsvs;
	}
	
	/**
	 * @return The number of CSVs in the partition.
	 */
	public int size() {
		return mCsvs.size();
	}
	
	/**
	 * @return a single CSV provider containing all groups from the partition.
	 */
	public ICsvProvider<T> toCsvProvider() {
		if (mCsvs.isEmpty()) {
			return new SimpleCsvProvider<>(Collections.emptyList());
		}
		
		// we assume that all CSVs have the same column titles
		final SimpleCsvProvider<T> result = new SimpleCsvProvider<>(mCsvs.iterator().next().getColumnTitles());
		
		for (final ICsvProvider<T> csv : mCsvs) {
			final int numberOfRows = csv.getRowHeaders().size();
			for (int i = 0; i < numberOfRows; ++i) {
				result.addRow(csv.getRowHeaders().get(i), csv.getRow(i));
			}
		}
		
		return result;
	}
	
	/**
	 * @return A fresh object with copied data.
	 */
	public CsvProviderPartition<T> copy() {
		final Collection<ICsvProvider<T>> partitionCopy = new ArrayList<>();
		for (final ICsvProvider<T> csv : mCsvs) {
			final ICsvProvider<T> csvCopy = new SimpleCsvProvider<>(csv.getColumnTitles());
			partitionCopy.add(csvCopy);
			final int numberOfRows = csv.getRowHeaders().size();
			for (int i = 0; i < numberOfRows; ++i) {
				csvCopy.addRow(new ArrayList<>(csv.getRow(i)));
			}
		}
		return new CsvProviderPartition<>(partitionCopy);
	}
	
	/**
	 * @param transformer
	 *            Transformer which is applied to each group.
	 */
	public void transform(final ICsvProviderTransformer<T> transformer) {
		final List<ICsvProvider<T>> transformedCsvs = new ArrayList<>(mCsvs.size());
		for (final ICsvProvider<T> csv : mCsvs) {
			transformedCsvs.add(transformer.transform(csv));
		}
		mCsvs = transformedCsvs;
	}
	
	/**
	 * @param predicate
	 *            Predicate on CSV; returns {@code true} iff the CSV should remain, otherwise the CSV is discarded.
	 */
	public void filterGroups(final Predicate<ICsvProvider<T>> predicate) {
		final Collection<ICsvProvider<T>> filteredCsvs = new ArrayList<>(mCsvs.size());
		for (final ICsvProvider<T> csv : mCsvs) {
			if (predicate.test(csv)) {
				filteredCsvs.add(csv);
			}
		}
		if (filteredCsvs.size() < mCsvs.size()) {
			mCsvs = filteredCsvs;
		}
	}
	
	/**
	 * NOTE: The method has two use cases. Either {@code thresholds} is {@code null}, then we use a {@link HashMap} with
	 * the entry in the defined column as key. Or {@code thresholds} has a value, then we use thresholds to pack the
	 * data (assumed to be {@code Integer}s) into bins.
	 */
	private List<ICsvProvider<T>> groupByColumnKeyAndThreshold(final ICsvProvider<T> csv, final String column,
			final int[] thresholds) {
		final int columnIndex = csv.getColumnTitles().indexOf(column);
		if (columnIndex == -1) {
			throw new IllegalArgumentException("The CSV key does not exist: " + column);
		}
		
		final Map<T, ICsvProvider<T>> key2group;
		final Map<Integer, ICsvProvider<T>> bin2group;
		if (thresholds == null) {
			key2group = new HashMap<>();
			bin2group = null;
		} else {
			key2group = null;
			bin2group = new TreeMap<>();
		}
		
		final int numberOfRows = csv.getRowHeaders().size();
		for (int i = 0; i < numberOfRows; ++i) {
			final List<T> row = csv.getRow(i);
			final T entry = row.get(columnIndex);
			assert thresholds == null || entry instanceof Integer;
			final int bin = getBin(entry, thresholds);
			ICsvProvider<T> group = (thresholds == null) ? key2group.get(entry) : bin2group.get(bin);
			final String rowTitle;
			if (group == null) {
				group = new SimpleCsvProvider<>(csv.getColumnTitles());
				if (thresholds == null) {
					key2group.put(entry, group);
					rowTitle = entry.toString();
				} else {
					bin2group.put(bin, group);
					final String lower = bin == 0 ? "(-\\infty" : "[" + Integer.toString(thresholds[bin - 1]);
					final String upper =
							bin == thresholds.length ? "\\infty)" : Integer.toString(thresholds[bin]) + "]";
					rowTitle = "$n \\in " + lower + "; " + upper + "$";
				}
			} else {
				final List<String> rowHeaders = group.getRowHeaders();
				rowTitle = rowHeaders.isEmpty()
						? entry.toString()
						: (rowHeaders.get(0) == null ? entry.toString() : rowHeaders.get(0));
			}
			group.addRow(rowTitle, new ArrayList<>(row));
		}
		
		final List<ICsvProvider<T>> result = new ArrayList<>();
		Collection<ICsvProvider<T>> csvs;
		if (thresholds == null) {
			csvs = key2group.values();
		} else {
			csvs = bin2group.values();
		}
		for (final ICsvProvider<T> group : csvs) {
			result.add(group);
		}
		return result;
	}
	
	private int getBin(final T entryRaw, final int[] thresholds) {
		if (thresholds == null) {
			return 0;
		}
		
		final int entry = Integer.parseInt(entryRaw.toString());
		
		for (int i = 0; i < thresholds.length; ++i) {
			if (entry < thresholds[i]) {
				return i;
			}
		}
		return thresholds.length;
	}
	
	/**
	 * Checks that all entries in a CSV are non-null. Since CSVs can originate from text files, we also check that the
	 * {@link #toString()} representation is different from "null".
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class AllEntriesNonNullFilter implements Predicate<ICsvProvider<T>> {
		@Override
		public boolean test(final ICsvProvider<T> csv) {
			final int numberOfRows = csv.getRowHeaders().size();
			for (int i = 0; i < numberOfRows; ++i) {
				final List<T> row = csv.getRow(i);
				for (final T entry : row) {
					if (entry == null || "null".equals(entry.toString())) {
						return false;
					}
				}
			}
			return true;
		}
	}
}
