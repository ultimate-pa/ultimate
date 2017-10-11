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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Data structure that can be used to partition a set of elements {@code <E>}.
 * http://en.wikipedia.org/wiki/Disjoint-set_data_structure Each equivalence
 * class has a unique representative. This implementation uses HashMaps - to
 * store for each element its equivalence class and - to store for each
 * equivalence class the representative
 *
 * @author Matthias Heizmann
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <E>
 *            element type
 */
public class UnionFind<E> implements IPartition<E>, Cloneable {
	/**
	 * Computes a new UnionFind instance whose partitions are the intersections of
	 * the given UnionFind instance's equivalence classes. Only non-empty
	 * intersections are added to the new equivalence relation.
	 *
	 * @param <E>
	 *            element type
	 * @param uf1
	 *            instance to be intersected with uf2
	 * @param uf2
	 *            instance to be intersected with uf1
	 * @return UnionFind with intersected equivalence classes
	 */
	public static <E> UnionFind<E> intersectPartitionBlocks(final UnionFind<E> uf1, final UnionFind<E> uf2) {
		assert uf1.mElementComparator == uf2.mElementComparator;

		final UnionFind<E> result = new UnionFind<>(uf1.mElementComparator);
		for (final Set<E> uf1Block : uf1.getAllEquivalenceClasses()) {
			final HashRelation<E, E> uf2RepToSubblock = new HashRelation<>();

			for (final E uf1El : uf1Block) {
				final E uf2Rep = uf2.find(uf1El);
				uf2RepToSubblock.addPair(uf2Rep, uf1El);
			}

			uf2RepToSubblock.getDomain().stream()
					.forEach(u2rep -> result.addEquivalenceClass(uf2RepToSubblock.getImage(u2rep)));
		}
		assert result.representativesAreMinimal();
		return result;
	}

	/**
	 * Computes a new UnionFind instance whose partitions are the unions of the
	 * given UnionFind instance's equivalence classes.
	 *
	 * @param <E>
	 *            element type
	 * @param uf1
	 *            instance to be union'ed with uf2
	 * @param uf2
	 *            instance to be union'ed with uf1
	 * @return UnionFind with union'ed equivalence classes
	 */
	public static <E> UnionFind<E> unionPartitionBlocks(final UnionFind<E> uf1, final UnionFind<E> uf2) {
		assert uf1.mElementComparator == uf2.mElementComparator;

		final UnionFind<E> result = new UnionFind<>(uf1.mElementComparator);
		final HashSet<E> todo = new HashSet<>(uf1.getAllElements());
		while (!todo.isEmpty()) {
			final E tver1El = todo.iterator().next();

			final E uf1Rep = uf1.find(tver1El);
			final E uf2Rep = uf2.find(tver1El);

			final E newBlockRep;
			if (uf1.mElementComparator == null) {
				// it does not matter which representative we choose
				newBlockRep = uf1Rep;
			} else {
				newBlockRep = uf1.mElementComparator.compare(uf1Rep, uf2Rep) < 0 ? uf1Rep : uf2Rep;
			}

			final Set<E> newBlock = DataStructureUtils.union(uf1.getEquivalenceClassMembers(tver1El),
					uf2.getEquivalenceClassMembers(tver1El));
			result.addEquivalenceClass(newBlock, newBlockRep);
			todo.removeAll(newBlock);
		}
		assert result.representativesAreMinimal();
		return result;
	}

	/**
	 * Comparator for elements. Our convention is that the representative of an
	 * equivalence class must always be a minimal element within the class in terms
	 * of this comparator.
	 * <p>
	 * Use of the comparator is optional, if no element comparator is present, this
	 * class may choose any representative for each equivalence class.
	 */
	private final Comparator<E> mElementComparator;

	/**
	 * Maps an element to its equivalence class.
	 */
	private final Map<E, Set<E>> mEquivalenceClass = new HashMap<>();

	/**
	 * Maps an equivalence class to its representative.
	 */
	// TODO This data-structure forms a performance bottleneck due to the usage of a
	// collection as key (e.g. hashcode calculation in Map#get). Check whether it
	// can be exchanged by a Map which stores keys by a fast-computed O(1) hashcode,
	// e.g. IdentityHashMap. Requirements are to maintain a deterministic iteration
	// order and to not fail at current, and also future, provided methods.
	private final Map<Set<E>, E> mRepresentative = new HashMap<>();

	/**
	 * Constructor for new (empty) data structure.
	 */
	public UnionFind() {
		mElementComparator = null;
	}

	/**
	 * Constructor for an empty union find data structure. Additionally takes a
	 * function that is used as a comparator between elements. (See the field's
	 * documentation for more details.)
	 */
	public UnionFind(final Comparator<E> elementComparator) {
		assert elementComparator != null : "use other constructor in this case!";
		mElementComparator = elementComparator;
	}

	/**
	 * Copy constructor.
	 *
	 * @param unionFind
	 *            the UnionFind instance to be copied
	 */
	protected UnionFind(final UnionFind<E> unionFind) {
		for (final Entry<Set<E>, E> entry : unionFind.mRepresentative.entrySet()) {
			final E representative = entry.getValue();
			final Set<E> equivalenceClassCopy = new HashSet<>(entry.getKey());
			for (final E equivalenceClassMember : equivalenceClassCopy) {
				final Set<E> oldValue = this.mEquivalenceClass.put(equivalenceClassMember, equivalenceClassCopy);
				assert oldValue == null : "element was contained twice";
			}
			this.mRepresentative.put(equivalenceClassCopy, representative);
		}
		mElementComparator = unionFind.mElementComparator;
		assert representativesAreMinimal();
	}

	/**
	 * Add a whole equivalence class at once to this UnionFind.
	 *
	 * Assumes none of the given elements is part of an existing equivalence class
	 * in this UnionFind instance.
	 *
	 * @param newBlock
	 */
	public void addEquivalenceClass(final Set<E> newBlock) {
		if (mElementComparator == null) {
			addEquivalenceClass(newBlock, null);
		} else {
			addEquivalenceClass(newBlock, findMinimalElement(newBlock));
		}
		assert representativesAreMinimal();
	}

	/**
	 * A variant of {@link #addEquivalenceClass(Set)} where the caller specifies the
	 * representative that the newly added equivalence class must have.
	 *
	 * @param newBlock
	 *            new equivalence class that is to be added to the equivalence
	 *            relation
	 * @param newBlockRep
	 *            the element that should be the representative of newBlock in this
	 *            UnionFind, null for don't care
	 */
	public void addEquivalenceClass(final Set<E> newBlock, final E newBlockRep) {
		assert DataStructureUtils.intersection(newBlock, getAllElements()).isEmpty();
		assert !newBlock.isEmpty();
		assert newBlockRep == null || newBlock.contains(newBlockRep);
		assert mElementComparator == null || newBlockRep != null : "if we don't give a representative for the new block"
				+ "here, this method might violate the invariant that the representative is always the minimal "
				+ "element.";

		final Set<E> block = new HashSet<>(newBlock);

		for (final E elem : block) {
			mEquivalenceClass.put(elem, block);
		}

		final E rep = newBlockRep == null ? block.iterator().next() : newBlockRep;
		assert mEquivalenceClass.get(rep) != null;
		mRepresentative.put(block, rep);
		assert representativesAreMinimal();
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Object#clone()
	 */
	@Override
	public UnionFind<E> clone() {
		return new UnionFind<>(this);
	}

	/**
	 * @param elem
	 *            element
	 * @return the representative of the equivalence class of element elem. null if
	 *         the given element is not in any equivalence class
	 */
	public E find(final E elem) {
		final Set<E> set = mEquivalenceClass.get(elem);
		return mRepresentative.get(set);
	}

	/**
	 * @param elem
	 *            element
	 * @return the representative of the equivalence class of element e. If there is
	 *         no equivalence class for e this equivalence class is constructed.
	 */
	public E findAndConstructEquivalenceClassIfNeeded(final E elem) {
		final E findResult = find(elem);
		if (findResult == null) {
			makeEquivalenceClass(elem);
			return elem;
		}
		return findResult;
	}

	public Set<E> getAllElements() {
		return Collections.unmodifiableSet(mEquivalenceClass.keySet());
	}

	/**
	 * Returns a collection of all equivalence classes. A equivalence class is an
	 * unmodifiable set that contains elements. Each contained element is only in
	 * one equivalence class.
	 *
	 * @return A collection of all equivalence classes. If there are no, the
	 *         collection is empty.
	 */
	public Collection<Set<E>> getAllEquivalenceClasses() {
		final Collection<Set<E>> allEquivalenceClasses = new LinkedList<>();
		for (final E representative : getAllRepresentatives()) {
			allEquivalenceClasses.add(getEquivalenceClassMembers(representative));
		}
		return allEquivalenceClasses;
	}

	/**
	 * @return collection of all elements e such that e is representative of an
	 *         equivalence class.
	 */
	public Collection<E> getAllRepresentatives() {
		return Collections.unmodifiableCollection(mRepresentative.values());
	}

	@Override
	public Set<E> getContainingSet(final E elem) {
		return getEquivalenceClassMembers(elem);
	}

	public Comparator<E> getElementComparator() {
		return mElementComparator;
	}

	/**
	 * @param elem
	 *            element
	 * @return set of all elements that are in the same equivalence class than e.
	 *         (Returned set also contains e).
	 */
	public Set<E> getEquivalenceClassMembers(final E elem) {
		return Collections.unmodifiableSet(mEquivalenceClass.get(elem));
	}

	@Override
	public Iterator<Set<E>> iterator() {
		return getAllEquivalenceClasses().iterator();
	}

	/**
	 * Construct a new equivalence class that is a singleton and contains only
	 * element e.
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

	/**
	 * Removes the given element from all the equivalence classes. If the element
	 * was a representative and was not the only element of its equivalence class,
	 * another representative for it is chosen for the new equivalence class.
	 *
	 * @param element
	 *            element to be removed
	 */
	public void remove(final E element) {
		final Set<E> eqc = mEquivalenceClass.get(element);
		final HashSet<E> newEqc = new HashSet<>(eqc);
		newEqc.remove(element);

		if (mRepresentative.get(mEquivalenceClass.get(element)).equals(element)) {
			// element is the representative of its equivalence class
			// final Set<E> eqc = mEquivalenceClass.get(element);
			if (eqc.size() == 1) {
				// element was alone in its equivalence class
				mEquivalenceClass.remove(element);
				mRepresentative.remove(eqc);
				assert areMembersConsistent();
				return;
			}

			// pick another element from the equivalence class, and make it the
			// representative
			if (mElementComparator == null) {
				final Iterator<E> it = eqc.iterator();
				E other = it.next();
				if (other.equals(element)) {
					other = it.next();
				}
				mRepresentative.put(eqc, other);
			} else {
				mRepresentative.put(eqc, findMinimalElement(newEqc));
			}
		}

		for (final E eqcEl : newEqc) {
			mEquivalenceClass.put(eqcEl, newEqc);
		}
		mEquivalenceClass.remove(element);

		final E rep = mRepresentative.get(eqc);
		mRepresentative.remove(eqc);
		assert !rep.equals(element);
		mRepresentative.put(newEqc, rep);

		assert areMembersConsistent();
		assert representativesAreMinimal();
	}

	/**
	 * Removes all given elements from all the equivalence classes. If an element
	 * was a representative and was not the only element of its equivalence class,
	 * another representative for it is chosen for the new equivalence class.
	 *
	 * @param elements
	 *            The elements to remove
	 */
	public void removeAll(final Collection<E> elements) {
		elements.forEach(this::remove);
	}

	/**
	 * @return number of equivalence classes.
	 */
	@Override
	public int size() {
		return mRepresentative.size();
	}

	@Override
	public String toString() {
		return mRepresentative.toString();
	}

	public void transformElements(final Function<E, E> elemTransformer) {
		final HashMap<Set<E>, E> representativeCopy = new HashMap<>(mRepresentative);
		for (final Entry<Set<E>, E> entry : representativeCopy.entrySet()) {
			for (final E oldElem : entry.getKey()) {
				mEquivalenceClass.remove(oldElem);
			}
			mRepresentative.remove(entry.getKey());

			final E newRep = elemTransformer.apply(entry.getValue());

//			assert mElementComparator == null || mElementComparator.compare(newRep, entry.getValue()) == 0;

			final Set<E> newEqClass = entry.getKey().stream().map(elemTransformer).collect(Collectors.toSet());
			for (final E newElem : newEqClass) {
				mEquivalenceClass.put(newElem, newEqClass);
			}
			mRepresentative.put(newEqClass, newRep);
		}
		assert representativesAreMinimal();
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
	 * Merge the equivalence classes of the elements e1 and e2. (e1 and e2 do not
	 * have to be the representatives of this equivalence classes).
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

		final E newRep;
		if (mElementComparator != null) {
			final E rep1 = mRepresentative.get(set1);
			final E rep2 = mRepresentative.get(set2);
			newRep = mElementComparator.compare(rep1, rep2) > 0 ? rep2 : rep1;
		} else {
			newRep = mRepresentative.get(largerSet);
		}

		mRepresentative.remove(largerSet);
		mRepresentative.remove(smallerSet);
		largerSet.addAll(smallerSet);
		for (final E e : smallerSet) {
			mEquivalenceClass.put(e, largerSet);
		}
		mRepresentative.put(largerSet, newRep);
		assert representativesAreMinimal();
	}

	private boolean areMembersConsistent() {
		for (final E e : mRepresentative.values()) {
			if (!mEquivalenceClass.containsKey(e)) {
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

	private E findMinimalElement(final Set<E> newBlock) {
		assert !newBlock.isEmpty();
		final Iterator<E> newBlockIt = newBlock.iterator();
		E result = newBlockIt.next();
		while (newBlockIt.hasNext()) {
			final E current = newBlockIt.next();
			result = mElementComparator.compare(current, result) < 0 ? current : result;
		}
		return result;
	}

	private boolean representativesAreMinimal() {
		if (mElementComparator == null) {
			return true;
		}
		// for (Entry<E, Set<E>> en : mEquivalenceClass.entrySet()) {
		for (final Entry<Set<E>, E> en : mRepresentative.entrySet()) {
			final E rep = en.getValue();
			for (final E member : en.getKey()) {
				assert mElementComparator.compare(rep, member) <= 0;
			}
		}
		return true;
	}
}
