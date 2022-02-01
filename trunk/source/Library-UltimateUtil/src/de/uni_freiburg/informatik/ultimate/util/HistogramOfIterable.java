/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Maps elements of an Iterable to the number of its occurrence. Visualizes this in a sorted array that lists the
 * occurrences of each element as follows. The array has one entry for each different (compared via .equals) element of
 * the Iterable. The array counts how often the entry occurs in the Iterable. The array is sorted wrt. a descending
 * order.
 *
 * @author Matthias Heizmann
 * @param <E>
 *            element type
 */
public class HistogramOfIterable<E> {
	private final Map<E, Integer> mHistogramMap;
	private final Integer[] mVisualizationArray;

	/**
	 * @param iterable
	 *            iterable
	 */
	public HistogramOfIterable(final Iterable<E> iterable) {
		mHistogramMap = generateHistogramMap(iterable);
		mVisualizationArray = generateVisualizationArray(mHistogramMap);
	}

	private Integer[] generateVisualizationArray(final Map<E, Integer> histogramMap) {
		final Integer[] result = histogramMap.values().toArray(new Integer[histogramMap.size()]);
		Arrays.sort(result, Collections.reverseOrder());
		return result;
	}

	@Override
	public String toString() {
		return Arrays.toString(mVisualizationArray);
	}

	public Integer[] getVisualizationArray() {
		return mVisualizationArray;
	}

	/**
	 * @return return the highest occurrence, return 0 if there are no elements
	 */
	public int getMax() {
		if (getVisualizationArray().length == 0) {
			return 0;
		}
		return getVisualizationArray()[0];
	}

	public static <E> Map<E, Integer> generateHistogramMap(final Iterable<E> iterable) {
		final Map<E, Integer> result = new HashMap<>();
		for (final E e : iterable) {
			if (result.containsKey(e)) {
				result.put(e, Integer.valueOf(result.get(e).intValue() + 1));
			} else {
				result.put(e, 1);
			}
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mHistogramMap == null) ? 0 : mHistogramMap.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final HistogramOfIterable<?> other = (HistogramOfIterable<?>) obj;
		if (mHistogramMap == null) {
			if (other.mHistogramMap != null) {
				return false;
			}
		} else if (!mHistogramMap.equals(other.mHistogramMap)) {
			return false;
		}
		return true;
	}

}
