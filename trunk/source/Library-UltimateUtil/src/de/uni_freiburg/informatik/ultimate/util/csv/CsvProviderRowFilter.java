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

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Removes rows from an {@link ICsvProvider}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderRowFilter<T> implements ICsvProviderTransformer<T> {
	private final Predicate<Pair<List<T>, List<String>>> mPredicate;
	
	/**
	 * Constructor.
	 * 
	 * @param predicate
	 *            row predicate which returns {@code true} iff the row should be added to the CSV.
	 */
	public CsvProviderRowFilter(final Predicate<Pair<List<T>, List<String>>> predicate) {
		mPredicate = predicate;
	}
	
	@Override
	public ICsvProvider<T> transform(final ICsvProvider<T> csvProvider) {
		final List<String> oldColumnTitles = csvProvider.getColumnTitles();
		final SimpleCsvProvider<T> result = new SimpleCsvProvider<>(oldColumnTitles);
		for (int i = 0; i < csvProvider.getRowHeaders().size(); ++i) {
			final List<T> row = csvProvider.getRow(i);
			if (mPredicate.test(new Pair<>(row, oldColumnTitles))) {
				result.addRow(row);
			}
		}
		return result;
	}
	
	/**
	 * A predicate which filters rows such that certain columns contain only predefined values.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <T>
	 *            CSV provider type
	 */
	public static class AllowedValuesRowFilter<T> implements Predicate<Pair<List<T>, List<String>>> {
		private final Map<String, Set<T>> mColumn2allowedValues;
		
		/**
		 * Constructor.
		 * 
		 * @param column2allowedValues
		 *            maps a column title to a set containing all values which are allowed in this column
		 */
		public AllowedValuesRowFilter(final Map<String, Set<T>> column2allowedValues) {
			mColumn2allowedValues = column2allowedValues;
		}
		
		@Override
		public boolean test(final Pair<List<T>, List<String>> pair) {
			final List<T> rowValues = pair.getFirst();
			final int size = pair.getSecond().size();
			final Iterator<String> iterator = pair.getSecond().iterator();
			/*
			 * TODO One could speed things up here if it runs too slowly for big tables by caching the column index
			 * during the first run and then only checking those.
			 * This would work under the (reasonable) assumption that all subsequent calls use the same column order.
			 */
			for (int i = 0; i < size; ++i) {
				final String columnTitle = iterator.next();
				final Set<T> allowedValues = mColumn2allowedValues.get(columnTitle);
				if (allowedValues == null) {
					// no filter for this column
					continue;
				}
				
				if (isForbiddenValue(rowValues.get(i), allowedValues)) {
					return false;
				}
			}
			return true;
		}
		
		protected boolean isForbiddenValue(final T value, final Set<T> allowedValues) {
			return !allowedValues.contains(value);
		}
	}
	
	/**
	 * A predicate which filters rows such that certain columns contain none of the predefined values.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <T>
	 *            CSV provider type
	 */
	public static class DisallowedValuesRowFilter<T> extends AllowedValuesRowFilter<T> {
		/**
		 * Constructor.
		 * 
		 * @param column2disallowedValues
		 *            maps a column title to a set containing all values which are not allowed in this column
		 */
		public DisallowedValuesRowFilter(final Map<String, Set<T>> column2disallowedValues) {
			super(column2disallowedValues);
		}
		
		@Override
		protected boolean isForbiddenValue(final T value, final Set<T> allowedValues) {
			// invert the result
			return !super.isForbiddenValue(value, allowedValues);
		}
	}
	
	/**
	 * Checks that all entries in a CSV are non-null. Since CSVs can originate from text files, we also check that the
	 * {@link #toString()} representation is different from "null".
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public static class AllEntriesNonNullFilter<T> implements Predicate<Pair<List<T>, List<String>>> {
		@Override
		public boolean test(final Pair<List<T>, List<String>> pair) {
			final List<T> row = pair.getFirst();
			for (final T entry : row) {
				if (entry == null || "null".equals(entry.toString())) {
					return false;
				}
			}
			return true;
		}
	}
}
