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
		mCsvs = groupByColumnKey(csv, column);
	}
	
	public Iterable<ICsvProvider<T>> getCsvs() {
		return mCsvs;
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
				result.addRow(csv.getRow(i));
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
	
	private List<ICsvProvider<T>> groupByColumnKey(final ICsvProvider<T> csv, final String column) {
		final int columnIndex = csv.getColumnTitles().indexOf(column);
		if (columnIndex == -1) {
			throw new IllegalArgumentException("The CSV key does not exist: " + column);
		}
		
		final List<ICsvProvider<T>> result = new ArrayList<>();
		final Map<T, ICsvProvider<T>> key2group = new HashMap<>();
		
		final int numberOfRows = csv.getRowHeaders().size();
		for (int i = 0; i < numberOfRows; ++i) {
			final List<T> row = csv.getRow(i);
			final T entry = row.get(columnIndex);
			ICsvProvider<T> group = key2group.get(entry);
			if (group == null) {
				group = new SimpleCsvProvider<>(csv.getColumnTitles());
				result.add(group);
				key2group.put(entry, group);
			}
			group.addRow(new ArrayList<>(row));
		}
		return result;
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
