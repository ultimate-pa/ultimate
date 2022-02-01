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
import java.math.RoundingMode;
import java.util.List;
import java.util.ListIterator;

/**
 * Rounds all decimal numbers in the data of an {@link ICsvProvider} to a fixed number of places after the point.
 * <p>
 * NOTE: Data contains shallow copies, i.e., modifications affect both the original data and this wrapper. Copy the
 * original to avoid such problems.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderRounding<T> implements ICsvProviderTransformer<T> {
	private final int mPlaces;
	
	/**
	 * @param places
	 *            The number of decimal places after the point.
	 */
	public CsvProviderRounding(final int places) {
		if (places < 0) {
			throw new IllegalArgumentException();
		}
		
		mPlaces = places;
	}
	
	@Override
	public ICsvProvider<T> transform(final ICsvProvider<T> csvProvider) {
		final List<String> rowTitles = csvProvider.getRowHeaders();
		for (int i = 0; i < rowTitles.size(); ++i) {
			final ListIterator<T> rowIt = csvProvider.getRow(i).listIterator();
			while (rowIt.hasNext()) {
				final T entry = rowIt.next();
				if (entry instanceof Double) {
					replaceDouble(rowIt, entry);
				} else if (entry instanceof String) {
					replaceString(rowIt, entry);
				}
			}
		}
		return csvProvider;
	}
	
	@SuppressWarnings("unchecked")
	private void replaceDouble(final ListIterator<T> rowIt, final T entry) {
		rowIt.set((T) round(new BigDecimal((Double) entry)));
	}
	
	@SuppressWarnings("unchecked")
	private void replaceString(final ListIterator<T> rowIt, final T entry) {
		try {
			final String rounded = round(new BigDecimal((String) entry)).toString();
			final String result;
			if (mPlaces == 0) {
				// remove trailing ".0"
				result = rounded.substring(0, rounded.length() - 2);
			} else {
				result = rounded;
			}
			rowIt.set((T) result);
		} catch (final NumberFormatException e) {
			// no Double string, ignore
		}
	}
	
	private Double round(final BigDecimal bigDecimal) {
		final BigDecimal rounded = bigDecimal.setScale(mPlaces, RoundingMode.HALF_UP);
		return rounded.doubleValue();
	}
}
