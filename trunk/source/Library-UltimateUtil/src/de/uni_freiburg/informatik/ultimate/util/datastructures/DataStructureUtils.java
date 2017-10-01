/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DataStructureUtils {

	private DataStructureUtils() {
		// do not instantiate
	}

	/**
	 * Constructs a new {@link Set} that contains only elements that occur in set1 and that occur in set2.
	 */
	public static <T> Set<T> intersection(final Set<T> set1, final Set<T> set2) {
		final Set<T> larger;
		final Set<T> smaller;
		if (set1.size() > set2.size()) {
			larger = set1;
			smaller = set2;
		} else {
			larger = set2;
			smaller = set1;
		}
		return smaller.stream().filter(larger::contains).collect(Collectors.toSet());
	}

	/**
	 * Construct a {@link Set} that contains all elements of set1 that are not in set2.
	 */
	public static <T> Set<T> difference(final Set<T> a, final Set<T> b) {
		return a.stream().filter(elem -> !b.contains(elem)).collect(Collectors.toSet());
	}

	/**
	 * Construct a {@link Set} that contains all elements of set1 and set2.
	 */
	public static <T> Set<T> union(final Set<T> a, final Set<T> b) {
		final Set<T> rtr = DataStructureUtils.getFreshSet(a, a.size() + b.size());
		rtr.addAll(b);
		return rtr;
	}

	/**
	 * Construct a {@link Set} that contains all elements of oldSet and has the capacity of oldSet.
	 */
	public static <T> Set<T> getFreshSet(final Set<T> oldSet) {
		return DataStructureUtils.getFreshSet(oldSet, oldSet.size());
	}

	/**
	 * Construct a {@link Set} that contains all elements of oldSet and starts with an initial capacity.
	 */
	public static <T> Set<T> getFreshSet(final Set<T> oldSet, final int capacity) {
		final Set<T> rtr = new HashSet<>(capacity);
		rtr.addAll(oldSet);
		return rtr;
	}

}
