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

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

/**
 * Aggregates data of an {@link ICsvProvider}.
 * <p>
 * NOTE: Data contains shallow copies, i.e., modifications affect both the original data and this wrapper. Copy the
 * original to avoid such problems.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderAggregator<T> implements ICsvProviderTransformer<T> {
	/**
	 * Aggregation mode.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum Aggregation {
		/**
		 * Average/mean of numeric columns.
		 */
		AVERAGE,
		/**
		 * Sum of numeric columns.
		 */
		SUM,
		/**
		 * Ignored, i.e., removed from the CSV.
		 */
		IGNORE,
	}
	
	private final Map<String, Aggregation> mColumn2aggregation;
	private final String mCountColumnTitle;
	
	/**
	 * @param column2aggregation
	 *            Maps columns to aggregation mode.
	 */
	public CsvProviderAggregator(final Map<String, Aggregation> column2aggregation) {
		this(column2aggregation, null);
	}
	
	/**
	 * @param column2aggregation
	 *            Maps columns to aggregation mode.
	 * @param countColumnTitle
	 *            column title for a new column counting the elements (null for deactivation)<br>
	 *            NOTE: To this feature, the CSV entries must be of type {@link String}.
	 */
	public CsvProviderAggregator(final Map<String, Aggregation> column2aggregation, final String countColumnTitle) {
		mColumn2aggregation = column2aggregation;
		mCountColumnTitle = countColumnTitle;
	}
	
	/**
	 * Aggregates a CSV.
	 * 
	 * @param csv
	 *            CSV
	 * @return aggregates CSV
	 */
	@SuppressWarnings("unchecked")
	@Override
	public ICsvProvider<T> transform(final ICsvProvider<T> csv) {
		final List<String> rowHeaders = csv.getRowHeaders();
		final int rows = rowHeaders.size();
		final ArrayList<String> columnTitles = new ArrayList<>();
		if (rows == 0) {
			return new SimpleCsvProvider<>(columnTitles);
		}
		
		final int columnsOld = csv.getColumnTitles().size();
		
		final boolean[] useColumn = new boolean[columnsOld];
		int index = 0;
		for (final String columnTitle : csv.getColumnTitles()) {
			final Aggregation aggregation = mColumn2aggregation.get(columnTitle);
			if (aggregation == null) {
				System.err.println("Ignoring column " + columnTitle + " which was not specified.");
				mColumn2aggregation.put(columnTitle, Aggregation.IGNORE);
			} else if (aggregation != Aggregation.IGNORE) {
				columnTitles.add(columnTitle);
				useColumn[index] = true;
			}
			++index;
		}
		columnTitles.trimToSize();
		isCountColumnFresh(columnTitles);
		
		final List<T> aggRow = filter(csv.getRow(0), useColumn, columnTitles.size());
		for (int i = 1; i < rows; ++i) {
			final List<T> row = csv.getRow(i);
			final List<T> filteredRow = filter(row, useColumn, columnTitles.size());
			aggregateRows(aggRow, filteredRow, columnTitles, i);
		}
		
		List<String> columnTitlesEnhanced;
		if (mCountColumnTitle != null) {
			// insert count
			columnTitlesEnhanced = new ArrayList<>(columnTitles.size() + 1);
			for (int i = 0; i < columnTitles.size(); ++i) {
				columnTitlesEnhanced.add(columnTitles.get(i));
			}
			columnTitlesEnhanced.add(mCountColumnTitle);
			if (!csv.getRow(0).isEmpty() && csv.getRow(0).get(0) instanceof String) {
				aggRow.add((T) Integer.toString(rowHeaders.size()));
			} else {
				throw new IllegalArgumentException(
						"Aggregation with adding a count column only works if the CSV has type String.");
			}
		} else {
			columnTitlesEnhanced = columnTitles;
		}
		
		final ICsvProvider<T> result = new SimpleCsvProvider<>(columnTitlesEnhanced);
		final String rowHeader = rowHeaders.get(0);
		result.addRow(rowHeader, aggRow);
		return result;
	}
	
	private void aggregateRows(final List<T> aggregatedRow, final List<T> singleRow, final List<String> columnTitles,
			final int numberOfAggregationsSoFar) {
		final ListIterator<T> aggIt = aggregatedRow.listIterator();
		final ListIterator<T> singleIt = singleRow.listIterator();
		final ListIterator<String> columnTitlesIt = columnTitles.listIterator();
		for (int i = 0; i < aggregatedRow.size(); ++i) {
			final T aggEntry = aggIt.next();
			final T singleEntry = singleIt.next();
			final String columnTitle = columnTitlesIt.next();
			final Aggregation agg = mColumn2aggregation.get(columnTitle);
			assert agg != null;
			switch (agg) {
				case AVERAGE:
					aggIt.set(getAverage(aggEntry, singleEntry, numberOfAggregationsSoFar));
					break;
				case SUM:
					aggIt.set(getSum(aggEntry, singleEntry, numberOfAggregationsSoFar));
					break;
				case IGNORE:
					assert false;
					break;
				default:
					throw new IllegalArgumentException("Unknown aggregation mode: " + agg);
			}
		}
	}

	private List<T> filter(final List<T> row, final boolean[] useColumn, final int length) {
		int i = 0;
		final List<T> result = new ArrayList<>(length);
		for (final T entry : row) {
			assert i < useColumn.length;
			if (useColumn[i]) {
				result.add(entry);
			}
			++i;
		}
		return result;
	}
	
	/**
	 * The mean of k+1 samples can be computed given the mean of k samples and one more sample as follows:<br>
	 * {@code m(k+1) = m(k) + 1/(k+1) * (x - m(k))}
	 */
	private T getAverage(final T aggEntryRaw, final T singleEntryRaw, final int numberOfSamples) {
		final double aggEntry = Double.parseDouble(aggEntryRaw.toString());
		final double singleEntry = Double.parseDouble(singleEntryRaw.toString());
		final double result = aggEntry + 1.0 / (numberOfSamples + 1) * (singleEntry - aggEntry);
		return getTypeFromDouble(result, aggEntryRaw);
	}
	
	private T getSum(final T aggEntryRaw, final T singleEntryRaw, final int numberOfSamples) {
		final double aggEntry = Double.parseDouble(aggEntryRaw.toString());
		final double singleEntry = Double.parseDouble(singleEntryRaw.toString());
		final double result = aggEntry + singleEntry;
		return getTypeFromDouble(result, aggEntryRaw);
	}
	
	@SuppressWarnings("unchecked")
	private T getTypeFromDouble(final Double d, final T typeSample) {
		if (typeSample instanceof Double) {
			return (T) d;
		}
		if (typeSample instanceof String) {
			return (T) BigDecimal.valueOf(d).toPlainString();
		}
		throw new IllegalArgumentException(
				"Received data not of type Double but of type " + typeSample.getClass().toGenericString());
	}
	
	private void isCountColumnFresh(final ArrayList<String> columnTitles) {
		if (mCountColumnTitle != null && columnTitles.contains(mCountColumnTitle)) {
			throw new IllegalArgumentException();
		}
	}
}
