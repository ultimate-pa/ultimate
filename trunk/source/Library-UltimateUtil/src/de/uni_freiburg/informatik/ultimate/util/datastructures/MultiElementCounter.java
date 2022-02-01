/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Counter that stores one number for each given object of type E.
 * Counting starts with 0.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <E>
 */
public class MultiElementCounter<E> {
	private final Map<E, Integer> mCounter = new HashMap<E, Integer>();

	/**
	 * Increase the counter for element by one and return the
	 * increased number.
	 */
	public Integer increment(final E element) {
		final Integer lastIndex = mCounter.get(element);
		final Integer newIndex;
		if (lastIndex == null) {
			newIndex = 1;
		} else {
			newIndex = lastIndex + 1;
		}
		mCounter.put(element, newIndex);
		return newIndex;
	}


	/**
	 * Increase the counter for element by k and return the
	 * increased number.
	 */
	public Integer increment(final E element, final int k) {
		final Integer lastIndex = mCounter.get(element);
		final Integer newIndex;
		if (lastIndex == null) {
			newIndex = k;
		} else {
			newIndex = lastIndex + k;
		}
		mCounter.put(element, newIndex);
		return newIndex;
	}

	/**
	 * @return the number that is stored for elem
	 */
	public Integer getNumber(final E elem) {
		final Integer number = mCounter.get(elem);
		if (number == null) {
			return 0;
		} else {
			return number;
		}
	}

	/**
	 * @return the set of all elements for which a number is stored
	 */
	public Set<E> getElements() {
		return mCounter.keySet();
	}

	public static <E> MultiElementCounter<E> add(final MultiElementCounter<E> mec1, final MultiElementCounter<E> mec2) {
		final Set<E> allElems =  new HashSet<>(mec1.getElements());
		allElems.addAll(mec2.getElements());
		final MultiElementCounter<E> result = new MultiElementCounter<>();
		for (final E elem : allElems) {
			final int sum = mec1.getNumber(elem) + mec2.getNumber(elem);
			result.increment(elem, sum);
		}
		return result;
	}


	@Override
	public String toString() {
		return String.valueOf(mCounter);
	}


}
