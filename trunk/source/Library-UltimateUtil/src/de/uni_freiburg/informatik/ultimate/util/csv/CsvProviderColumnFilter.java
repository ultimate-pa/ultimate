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
import java.util.Iterator;
import java.util.List;
import java.util.function.Predicate;

/**
 * Removes columns from an {@link ICsvProvider}.
 * <p>
 * The filter is based on the column title only.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderColumnFilter<T> implements ICsvProviderTransformer<T> {
	private final Predicate<String> mPredicate;
	
	/**
	 * Constructor.
	 * 
	 * @param predicate
	 *            column predicate which returns {@code true} iff the column should be added to the CSV
	 */
	public CsvProviderColumnFilter(final Predicate<String> predicate) {
		mPredicate = predicate;
	}
	
	@Override
	@SuppressWarnings("squid:S1994")
	public ICsvProvider<T> transform(final ICsvProvider<T> csvProvider) {
		final List<String> oldColumnTitles = csvProvider.getColumnTitles();
		final ArrayList<String> newColumnTitles = new ArrayList<>(oldColumnTitles.size());
		
		// filter columns
		final boolean[] retainedColumnsMask = new boolean[oldColumnTitles.size()];
		final Iterator<String> colIt = oldColumnTitles.iterator();
		for (int i = 0; i < retainedColumnsMask.length; ++i) {
			final String oldColumnTitle = colIt.next();
			if (mPredicate.test(oldColumnTitle)) {
				newColumnTitles.add(oldColumnTitle);
				retainedColumnsMask[i] = true;
			}
		}
		newColumnTitles.trimToSize();
		
		// if nothing was filtered, return the original object
		if (newColumnTitles.size() == oldColumnTitles.size()) {
			return csvProvider;
		}
		
		// create new CsvProvider
		final SimpleCsvProvider<T> result = new SimpleCsvProvider<>(newColumnTitles);
		
		// add old rows with filtered columns only
		for (int i = 0; i < csvProvider.getRowHeaders().size(); ++i) {
			final List<T> newRow = new ArrayList<>();
			final List<T> row = csvProvider.getRow(i);
			final Iterator<T> rowIt = row.iterator();
			for (int j = 0; j < row.size(); ++j) {
				final T elem = rowIt.next();
				if (retainedColumnsMask[j]) {
					newRow.add(elem);
				}
			}
			result.addRow(newRow);
		}
		
		return result;
	}
	
	/**
	 * A predicate which filters for certain names.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public static class NameFilter implements Predicate<String> {
		private final Collection<String> mFilterNames;
		
		/**
		 * Constructor.
		 * 
		 * @param allowedNames
		 *            names for which the test is positive
		 */
		public NameFilter(final Collection<String> allowedNames) {
			mFilterNames = allowedNames;
		}
		
		@Override
		public boolean test(final String name) {
			return mFilterNames.contains(name);
		}
	}
}
