/*
 * Copyright (C) 2015 mostafa.amin93@gmail.com
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * Class containing a variety of combinatorial utility functions.
 * @author mostafa.amin93@gmail.com
 *
 */
public class CombinatoricsUtils {

	private CombinatoricsUtils() {}

	/***
	 * Transform an iterator to a set.
	 * @param iter
	 * @return
	 */
	public static <T> Set<T> iterateAll(final Iterator<T> iter) {
		final Set<T> res = new HashSet<>();
		while(iter.hasNext()) {
			res.add(iter.next());
		}
		return res;
	}

	/***
	 * Transform an iterator to a set.
	 * @param iter
	 * @return
	 */
	public static <T> Set<T> iterateAll(final Iterable<T> iter) {
		final Set<T> res = new HashSet<>();
		for (final T s : iter) {
			res.add(s);
		}
		return res;
	}

	/***
	 * Get all possible r-tuples combined by a set of different values for each field.
	 * @param values
	 * @return
	 */
	public static <T> Set<List<T>> getCombinations(final List<Collection<T>> values) {
		return getCombinations(values, values.size());
	}

	private static <T> Set<List<T>> getCombinations(final List<Collection<T>> values, final int idx) {
		if (idx == 0) {
			final List<T> singleton = new ArrayList<>();
			final Set<List<T>> res = new HashSet<>();
			res.add(singleton);
			return res;
		}
		final Set<List<T>> oldCombinations = getCombinations(values, idx - 1);
		final Set<List<T>> res = new HashSet<>();
		for (final T newValue : values.get(idx - 1)) {
			for (final List<T> oldCombination : oldCombinations) {
				final List<T> combination = new ArrayList<>();
				combination.addAll(oldCombination);
				combination.add(newValue);
				res.add(combination);
			}
		}
		return res;
	}
}
