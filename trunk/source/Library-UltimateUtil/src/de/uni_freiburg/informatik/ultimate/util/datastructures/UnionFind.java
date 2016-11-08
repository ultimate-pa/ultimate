/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

/**
 * Data structure that can be used to partition a set of elements <E>.
 * http://en.wikipedia.org/wiki/Disjoint-set_data_structure Each equivalence class has a unique representative. This
 * implementation uses HashMaps - to store for each element its equivalence class and - to store for each equivalence
 * class the representative
 *
 * @author Matthias Heizmann
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public class UnionFind<E> {
	/**
	 * Maps an element to its equivalence class.
	 */
	private final Map<E, Set<E>> mEquivalenceClass = new HashMap<>();
	/**
	 * Maps an equivalence class to its representative.
	 */
	private final Map<Set<E>, E> mRepresentative = new HashMap<>();

	/**
	 * Returns the representative of the equivalence class of element e.
	 */
	public E find(final E e) {
		final Set<E> set = mEquivalenceClass.get(e);
		return mRepresentative.get(set);
	}

	/**
	 * Returns the representative of the equivalence class of element e. If there is no equivalence class for e this
	 * equivalence class is constructed.
	 */
	public E findAndConstructEquivalenceClassIfNeeded(final E e) {
		final E findResult = find(e);
		if (findResult == null) {
			makeEquivalenceClass(e);
			return e;
		}
		return findResult;
	}

	/**
	 * Returns a collection of all equivalence classes. A equivalence class is an unmodifiable set that contains
	 * elements. Each contained element is only in one equivalence class.
	 *
	 * @return A collection of all equivalence classes. If there are no, the collection is empty.
	 */
	public Collection<Set<E>> getAllEquivalenceClasses() {
		final Collection<Set<E>> allEquivalenceClasses = new LinkedList<>();
		for (final E representative : getAllRepresentatives()) {
			allEquivalenceClasses.add(getEquivalenceClassMembers(representative));
		}
		return allEquivalenceClasses;
	}

	/**
	 * Return collection of all elements e such that e is representative of an equivalence class.
	 */
	public Collection<E> getAllRepresentatives() {
		return mRepresentative.values();
	}

	/**
	 * Return set of all elements that are in the same equivalence class than e. (Returned set also contains e).
	 */
	public Set<E> getEquivalenceClassMembers(final E e) {
		return Collections.unmodifiableSet(mEquivalenceClass.get(e));
	}

	/**
	 * Construct a new equivalence class that is a singleton and contains only element e.
	 */
	public void makeEquivalenceClass(final E e) {
		if (mEquivalenceClass.containsKey(e)) {
			throw new IllegalArgumentException("Already contained " + e);
		}
		final Set<E> result = new HashSet<>();
		result.add(e);
		mEquivalenceClass.put(e, result);
		mRepresentative.put(result, e);
	}

	@Override
	public String toString() {
		return mRepresentative.toString();
	}

	/**
	 * Merge the equivalence classes of the elements e1 and e2. (e1 and e2 do not have to be the representatives of this
	 * equivalence classes).
	 */
	public void union(final E e1, final E e2) {
		final Set<E> set1 = mEquivalenceClass.get(e1);
		final Set<E> set2 = mEquivalenceClass.get(e2);
		final E set1rep = mRepresentative.get(set1);
		mRepresentative.remove(set1);
		mRepresentative.remove(set2);
		set1.addAll(set2);
		for (final E e : set2) {
			mEquivalenceClass.put(e, set1);
		}
		mRepresentative.put(set1, set1rep);
	}

	/**
	 * @return number of equivalence classes
	 */
	public int size() {
		return mRepresentative.size();
	}

}
