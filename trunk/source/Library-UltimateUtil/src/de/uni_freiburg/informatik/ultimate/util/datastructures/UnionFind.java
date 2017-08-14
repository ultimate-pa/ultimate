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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * Data structure that can be used to partition a set of elements {@code <E>}.
 * http://en.wikipedia.org/wiki/Disjoint-set_data_structure Each equivalence class has a unique representative. This
 * implementation uses HashMaps - to store for each element its equivalence class and - to store for each equivalence
 * class the representative
 *
 * @author Matthias Heizmann
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <E>
 *            element type
 */
public class UnionFind<E> implements IPartition<E> {
	/**
	 * Maps an element to its equivalence class.
	 */
	private final Map<E, Set<E>> mEquivalenceClass = new HashMap<>();
	/**
	 * Maps an equivalence class to its representative.
	 */
	private final Map<Set<E>, E> mRepresentative = new HashMap<>();

	/**
	 * Constructor for new (empty) data structure.
	 */
	public UnionFind() {

	}

	/**
	 * Copy constructor.
	 */
	public UnionFind(final UnionFind<E> unionFind) {
		for (final Entry<E, Set<E>> entry : unionFind.mEquivalenceClass.entrySet()) {
			final E representative = entry.getKey();
			final Set<E> equivalenceClassCopy = new HashSet<>(entry.getValue());
			assert mRepresentative.get(equivalenceClassCopy) == representative : "inconsitent";
			final Set<E> oldValue = this.mEquivalenceClass.put(representative, equivalenceClassCopy);
			assert oldValue == null : "element was contained twice";
			this.mRepresentative.put(equivalenceClassCopy, representative);
		}
	}

	/**
	 * @param elem
	 *            element
	 * @return the representative of the equivalence class of element e.
	 */
	public E find(final E elem) {
		final Set<E> set = mEquivalenceClass.get(elem);
		if (set == null) {
			return null;
		}
		return mRepresentative.get(set);
	}

	/**
	 * @param elem
	 *            element
	 * @return the representative of the equivalence class of element e. If there is no equivalence class for e this
	 *         equivalence class is constructed.
	 */
	public E findAndConstructEquivalenceClassIfNeeded(final E elem) {
		final E findResult = find(elem);
		if (findResult == null) {
			makeEquivalenceClass(elem);
			return elem;
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
	 * @return collection of all elements e such that e is representative of an equivalence class.
	 */
	public Collection<E> getAllRepresentatives() {
		return Collections.unmodifiableCollection(mRepresentative.values());
	}

	/**
	 * @param elem
	 *            element
	 * @return set of all elements that are in the same equivalence class than e. (Returned set also contains e).
	 */
	public Set<E> getEquivalenceClassMembers(final E elem) {
		return Collections.unmodifiableSet(mEquivalenceClass.get(elem));
	}

	@Override
	public Set<E> getContainingSet(final E elem) {
		return getEquivalenceClassMembers(elem);
	}

	/**
	 * Construct a new equivalence class that is a singleton and contains only element e.
	 *
	 * @param elem
	 *            element
	 */
	public void makeEquivalenceClass(final E elem) {
		if (mEquivalenceClass.containsKey(elem)) {
			throw new IllegalArgumentException("Already contained " + elem);
		}
		final Set<E> result = new HashSet<>();
		result.add(elem);
		mEquivalenceClass.put(elem, result);
		mRepresentative.put(result, elem);
	}

	@Override
	public String toString() {
		return mRepresentative.toString();
	}

	/**
	 * Merge the equivalence classes of the elements e1 and e2. (e1 and e2 do not have to be the representatives of this
	 * equivalence classes).
	 *
	 * @param elem1
	 *            first element
	 * @param elem2
	 *            second element
	 */
	public void union(final E elem1, final E elem2) {
		final Set<E> set1 = mEquivalenceClass.get(elem1);
		final Set<E> set2 = mEquivalenceClass.get(elem2);

		final boolean set1IsLarger = set1.size() > set2.size();

		final Set<E> largerSet = set1IsLarger ? set1 : set2;
		final Set<E> smallerSet = set1IsLarger ? set2 : set1;

		final E largerSetRep = mRepresentative.get(largerSet);
		mRepresentative.remove(largerSet);
		mRepresentative.remove(smallerSet);
		largerSet.addAll(smallerSet);
		for (final E e : smallerSet) {
			mEquivalenceClass.put(e, largerSet);
		}
		mRepresentative.put(largerSet, largerSetRep);
	}

	/**
	 * Union operation for arbitrary number of arguments.
	 *
	 * @param elements
	 *            elements
	 */
	public void union(final Collection<E> elements) {
		final Iterator<E> it = elements.iterator();
		if (!it.hasNext()) {
			return;
		}
		final E firstElem = it.next();
		while (it.hasNext()) {
			union(firstElem, it.next());
		}
	}

	/**
	 * @return number of equivalence classes.
	 */
	@Override
	public int size() {
		return mRepresentative.size();
	}

	@Override
	public Iterator<Set<E>> iterator() {
		return getAllEquivalenceClasses().iterator();
	}

	public void remove(final E element) {

		if (mRepresentative.get(mEquivalenceClass.get(element)).equals(element)) {
			// element is the representative of its equivalence class
			final Set<E> eqc = mEquivalenceClass.get(element);
			if (eqc.size() == 1) {
				// element was alone in its equivalence class
				mEquivalenceClass.remove(element);
				mRepresentative.remove(eqc);
				assert areMembersConsistent();
				return;
			}
			// pick another element from the equivalence class, and make it the representative
			final Iterator<E> it = eqc.iterator();
			E other = it.next();
			while (other.equals(element)) {
				other = it.next();
			}
			mRepresentative.put(eqc, other);
		}

		final Set<E> eqc = mEquivalenceClass.get(element);
		final HashSet<E> newEqc = new HashSet<>(eqc);
		newEqc.remove(element);
		for (final E eqcEl : newEqc) {
			mEquivalenceClass.put(eqcEl, newEqc);
		}
		mEquivalenceClass.remove(element);

		final E rep = mRepresentative.get(eqc);
		mRepresentative.remove(eqc);
		assert !rep.equals(element);
		mRepresentative.put(newEqc, rep);

		assert areMembersConsistent();
	}

	private boolean areMembersConsistent() {
		for (final E el : mRepresentative.values()) {
			if (!mEquivalenceClass.containsKey(el)) {
				return false;
			}
		}
		for (final Set<E> eqc : mEquivalenceClass.values()) {
			if (!mRepresentative.containsKey(eqc)) {
				return false;
			}
		}
		for (final Set<E> eqc : mRepresentative.keySet()) {
			if (!mEquivalenceClass.values().contains(eqc)) {
				return false;
			}
		}
		return true;
	}

	public Set<E> getAllElements() {
		return Collections.unmodifiableSet(mEquivalenceClass.keySet());
	}

	/**
	 * Add a whole equivalence class at once to this UnionFind.
	 *
	 * Assumes none of the given elements is part of an existing equivalence class in this UnionFind instance.
	 *
	 * @param block
	 */
	public void addEquivalenceClass(final Set<E> originalBlock) {
		assert !originalBlock.isEmpty();
		final Set<E> block = new HashSet<>(originalBlock);

		for (final E el : block) {
			mEquivalenceClass.put(el, block);
		}

		final E rep = block.iterator().next();
		assert mEquivalenceClass.get(rep) == null;
		mRepresentative.put(block, rep);
	}
}
