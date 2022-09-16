/*
 * Copyright (C) 2016-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Comparator for maps with values from a partially ordered set.
 *
 * Given two maps {@code m1} and {@code m2} we say that {@code m1} is less or equal {@code m2} if the following
 * conditions hold:
 * <ul>
 * <li>{@code m1.keySet()} is a subset of {@code m2.keySet()}</li>
 * <li>For all keys {@code k} of {@code m1}, the value {@code m1.get(k)} is less or equal {@code m2.get(k)}</li>
 * </ul>
 *
 * @author Matthias Heizmann
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <K>
 *            The type of keys (no ordering considered)
 * @param <V>
 *            The partially-ordered type of values
 */
public class CanonicalPartialComparatorForMaps<K, V> implements IPartialComparator<Map<K, V>> {
	private final IPartialComparator<V> mComparator;

	/**
	 * Create a new map comparator from a partial comparator for values.
	 *
	 * @param comparator
	 *            The comparator used to compare values in maps
	 */
	public CanonicalPartialComparatorForMaps(final IPartialComparator<V> comparator) {
		mComparator = comparator;
	}

	/**
	 * Create a new map comparator from a Java {@link Comparator} for values.
	 *
	 * @param comparator
	 *            the comparator used to compare values in maps
	 * @param isConsistent
	 *            whether or not the comparator is "consistent with equals". See
	 *            {@link IPartialComparator#fromNonPartialComparator(Comparator, boolean)} for details.
	 */
	public CanonicalPartialComparatorForMaps(final Comparator<V> comparator, final boolean isConsistent) {
		this(IPartialComparator.fromNonPartialComparator(comparator, isConsistent));
	}

	/**
	 * Create a new map comparator from a Java {@link Comparator} for values.
	 *
	 * For compatibility reasons, this assumes that the given comparator is "consistent with equals" (see
	 * {@link IPartialComparator#fromNonPartialComparator(Comparator, boolean)} for details.
	 *
	 * @param comparator
	 *            the comparator used to compare values in maps
	 */
	public CanonicalPartialComparatorForMaps(final Comparator<V> comparator) {
		this(comparator, true);
	}

	@Override
	public ComparisonResult compare(final Map<K, V> o1, final Map<K, V> o2) {
		if (o1 == o2) {
			// performance optimisation
			return ComparisonResult.EQUAL;
		}

		if (o1.size() > o2.size()) {
			// swap, so we always iterate over the smaller map (for performance)
			return compare(o2, o1).invert();
		}

		ComparisonResult result = ComparisonResult.EQUAL;
		for (final Entry<K, V> entry : o1.entrySet()) {
			ComparisonResult currentPartialComparionResult;
			final V value2 = o2.get(entry.getKey());
			if (value2 == null) {
				currentPartialComparionResult = ComparisonResult.STRICTLY_GREATER;
			} else {
				currentPartialComparionResult = mComparator.compare(entry.getValue(), value2);
			}
			result = ComparisonResult.aggregate(result, currentPartialComparionResult);
			if (result == ComparisonResult.INCOMPARABLE) {
				return result;
			}
		}

		if (result == ComparisonResult.EQUAL && o1.size() < o2.size()) {
			// not equal but strictly smaller since o2 has elements that o1 does not have.
			result = ComparisonResult.STRICTLY_SMALLER;
		} else if (result == ComparisonResult.STRICTLY_GREATER && !o1.keySet().containsAll(o2.keySet())) {
			// not strictly greater but incomparable since o2 has elements that o1 does not have.
			result = ComparisonResult.INCOMPARABLE;
		}
		return result;
	}

}
