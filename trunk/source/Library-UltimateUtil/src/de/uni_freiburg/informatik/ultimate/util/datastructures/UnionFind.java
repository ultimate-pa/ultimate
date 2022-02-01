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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Data structure that can be used to partition a set of elements {@code <E>}.
 * http://en.wikipedia.org/wiki/Disjoint-set_data_structure Each equivalence class has a unique representative. This
 * implementation uses HashMaps - to store for each element its equivalence class and - to store for each equivalence
 * class the representative
 *
 * @author Matthias Heizmann
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class UnionFind<E> implements IPartition<E>, Cloneable {
	/**
	 * Comparator for elements. Our convention is that the representative of an equivalence class must always be a
	 * minimal element within the class in terms of this comparator.
	 * <p>
	 * Use of the comparator is optional, if no element comparator is present, this class may choose any representative
	 * for each equivalence class.
	 */
	private final Comparator<E> mElementComparator;

	/**
	 * Maps an element to its equivalence class.<br/>
	 * <br/>
	 * Note that whenever updating values in this map other corresponding data-structures as {@link #mRepresentative}
	 * also need to be updated with the same new identity.
	 */
	private final Map<E, CachedHashSet<E>> mEquivalenceClass = new HashMap<>();

	/**
	 * Maps an equivalence class to its representative.<br/>
	 * <br/>
	 * The current implementation uses {@link CachedHashSet} to provide a fast key-based access.<br/>
	 * <br/>
	 * Therefore whenever changing keys in this set other corresponding data-structures like {@link #mEquivalenceClass}
	 * also need to be updated with the same new identity.
	 */
	private final Map<CachedHashSet<E>, E> mRepresentative = new HashMap<>();

	/**
	 * Constructor for new (empty) data structure.
	 */
	public UnionFind() {
		mElementComparator = null;
	}

	/**
	 * Constructor for an empty union find data structure. Additionally takes a function that is used as a comparator
	 * between elements. (See the field's documentation for more details.)
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
		for (final Entry<CachedHashSet<E>, E> entry : unionFind.mRepresentative.entrySet()) {
			final E representative = entry.getValue();
			final CachedHashSet<E> equivalenceClassCopy = new CachedHashSet<>(entry.getKey());
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
	 * Assumes none of the given elements is part of an existing equivalence class in this UnionFind instance.
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
	 * A variant of {@link #addEquivalenceClass(Set)} where the caller specifies the representative that the newly added
	 * equivalence class must have.
	 *
	 * @param newBlock
	 *            new equivalence class that is to be added to the equivalence relation
	 * @param newBlockRep
	 *            the element that should be the representative of newBlock in this UnionFind, null for don't care
	 */
	public void addEquivalenceClass(final Set<E> newBlock, final E newBlockRep) {
		assert DataStructureUtils.intersection(newBlock, getAllElements()).isEmpty();
		assert !newBlock.isEmpty();
		assert newBlockRep == null || newBlock.contains(newBlockRep);
		assert mElementComparator == null || newBlockRep != null : "if we don't give a representative for the new block"
				+ "here, this method might violate the invariant that the representative is always the minimal "
				+ "element.";
		assert mElementComparator == null || mElementComparator.compare(newBlockRep, findMinimalElement(newBlock)) <= 0;

		final CachedHashSet<E> block = new CachedHashSet<>(newBlock);

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
	 * @return the representative of the equivalence class of element elem. null if the given element is not in any
	 *         equivalence class
	 */
	public E find(final E elem) {
		final Set<E> set = mEquivalenceClass.get(elem);
		return mRepresentative.get(set);
	}

	public Set<E> find(final Set<E> elemSet) {
		final Set<E> result = new HashSet<>();
		for (final E elem : elemSet) {
			final E rep = find(elem);
			if (rep != null) {
				result.add(rep);
			}
		}
		return result;
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

	public Set<E> getAllElements() {
		return Collections.unmodifiableSet(mEquivalenceClass.keySet());
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
	 * @return set of all elements that are in the same equivalence class than e. (Returned set also contains e).
	 */
	public Set<E> getEquivalenceClassMembers(final E elem) {
		return Collections.unmodifiableSet(mEquivalenceClass.get(elem));
	}

	@Override
	public Iterator<Set<E>> iterator() {
		return getAllEquivalenceClasses().iterator();
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
		final CachedHashSet<E> result = new CachedHashSet<>();
		result.add(elem);
		mEquivalenceClass.put(elem, result);
		mRepresentative.put(result, elem);
	}

	/**
	 * Removes the given element from all the equivalence classes. If the element was a representative and was not the
	 * only element of its equivalence class, another representative for it is chosen for the new equivalence class.
	 *
	 * @param element
	 *            element to be removed
	 */
	public void remove(final E element) {
		remove(element, null);
	}

	/**
	 * Variant of remove(E) that allows the user to give a preference for which element should be the new representative
	 * of the equivalence class, if the removed element was the representative before.
	 *
	 * @param element
	 *            the element to be removed
	 * @param newRepChoice
	 *            must be in the same equivalence class as element; if the representative of element's equivalence class
	 *            is changed by this method, newRepChoice will be the new representative. If newRepChoice is given as
	 *            null, an arbitrary new representative will be chosen from the remaining members of element's
	 *            equivalence class.
	 */
	public void remove(final E element, final E newRepChoice) {
		assert newRepChoice == null || find(newRepChoice) == find(element);

		final CachedHashSet<E> eqc = mEquivalenceClass.get(element);
		final CachedHashSet<E> newEqc = new CachedHashSet<>(eqc);
		newEqc.remove(element);

		/*
		 * if eqc is non-empty after the remove, make sure it gets another representative (keeps the old eqc, for now,
		 * will replace it with newEqc in next step)
		 */
		if (mRepresentative.get(mEquivalenceClass.get(element)).equals(element)) {
			// element is the representative of its equivalence class

			if (eqc.size() == 1) {
				// element was alone in its equivalence class
				mEquivalenceClass.remove(element);
				mRepresentative.remove(eqc);
				assert areMembersConsistent();
				return;
			}

			// pick another element from the equivalence class, and make it the representative
			E newRep;
			if (mElementComparator == null) {
				if (newRepChoice == null) {
					newRep = newEqc.iterator().next();
				} else {
					assert newEqc.contains(newRepChoice);
					newRep = newRepChoice;
				}
			} else {
				final E minimum = findMinimalElement(newEqc);
				if (newRepChoice == null) {
					newRep = minimum;
				} else {
					if (mElementComparator.compare(newRepChoice, minimum) != 0) {
						throw new IllegalArgumentException(
								"newRepChoice must be compatible with the element " + "comparator!");
					}
					newRep = newRepChoice;
				}
			}
			mRepresentative.put(eqc, newRep);
		}

		/*
		 * Replace the old eqc by newEqc
		 */
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
	 * Removes all given elements from all the equivalence classes. If an element was a representative and was not the
	 * only element of its equivalence class, another representative for it is chosen for the new equivalence class.
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
		final HashMap<CachedHashSet<E>, E> representativeCopy = new HashMap<>(mRepresentative);
		for (final Entry<CachedHashSet<E>, E> entry : representativeCopy.entrySet()) {
			for (final E oldElem : entry.getKey()) {
				mEquivalenceClass.remove(oldElem);
			}
			mRepresentative.remove(entry.getKey());

			final E newRep = elemTransformer.apply(entry.getValue());

			final CachedHashSet<E> newEqClass =
					entry.getKey().stream().map(elemTransformer).collect(Collectors.toCollection(CachedHashSet::new));
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
	 * Merge the equivalence classes of the elements e1 and e2. (e1 and e2 do not have to be the representatives of this
	 * equivalence classes).
	 *
	 * @param elem1
	 *            first element
	 * @param elem2
	 *            second element
	 */
	public void union(final E elem1, final E elem2) {
		final CachedHashSet<E> set1 = mEquivalenceClass.get(elem1);
		final CachedHashSet<E> set2 = mEquivalenceClass.get(elem2);

		final boolean set1IsLarger = set1.size() > set2.size();

		final CachedHashSet<E> largerSet = set1IsLarger ? set1 : set2;
		final CachedHashSet<E> smallerSet = set1IsLarger ? set2 : set1;

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

	/**
	 * Computes a new UnionFind instance whose partitions are the intersections of the given UnionFind instance's
	 * equivalence classes. Only non-empty intersections are added to the new equivalence relation.
	 * <p>
	 * If the input UnionFind instances are viewed as elements of an abstract domain, the result corresponds to their
	 * abstract join.
	 * <p>
	 * Also returns a split info for each input UnionFind. A split info maps each representative in the original
	 * UnionFind to the (possibly many) corresponding representatives in the new UnionFind.
	 *
	 * @param <E>
	 *            element type
	 * @param uf1
	 *            instance to be intersected with uf2
	 * @param uf2
	 *            instance to be intersected with uf1
	 * @return UnionFind with intersected equivalence classes
	 */
	public static <E> Triple<UnionFind<E>, HashRelation<E, E>, HashRelation<E, E>>
			intersectPartitionBlocks(final UnionFind<E> uf1, final UnionFind<E> uf2) {
		assert uf1.mElementComparator == uf2.mElementComparator;

		final UnionFind<E> result = new UnionFind<>(uf1.mElementComparator);
		final HashRelation<E, E> uf1SplitInfo = new HashRelation<>();
		final HashRelation<E, E> uf2SplitInfo = new HashRelation<>();

		for (final Set<E> uf1Block : uf1.getAllEquivalenceClasses()) {
			final E uf1Rep = uf1.find(uf1Block.iterator().next());

			// map a representative of uf2 to the intersection of its block in uf2 with the current uf1Block
			final HashRelation<E, E> uf2RepToIntersection = new HashRelation<>();
			for (final E uf1El : uf1Block) {
				final E uf2Rep = uf2.find(uf1El);
				uf2RepToIntersection.addPair(uf2Rep, uf1El);
			}

			for (final E uf2Rep : uf2RepToIntersection.getDomain()) {
				final Set<E> intersection = uf2RepToIntersection.getImage(uf2Rep);

				// assert intersection.contains(uf2Rep) : "right?.."; // EDIT: not the case

				result.addEquivalenceClass(intersection);

				final E subBlockRep = result.find(intersection.iterator().next());

				uf1SplitInfo.addPair(uf1Rep, subBlockRep);
				uf2SplitInfo.addPair(uf2Rep, subBlockRep);
			}
		}
		assert result.representativesAreMinimal();
		assert sanityCheckIntersectPartitionBlocks(uf1, uf2, result, uf1SplitInfo, uf2SplitInfo);
		return new Triple<>(result, uf1SplitInfo, uf2SplitInfo);
	}

	/**
	 * Computes a new UnionFind instance whose partitions are the unions of the given UnionFind instance's equivalence
	 * classes.
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
		for (final Entry<CachedHashSet<E>, E> en : mRepresentative.entrySet()) {
			final E rep = en.getValue();
			for (final E member : en.getKey()) {
				assert mElementComparator.compare(rep, member) <= 0;
			}
		}
		return true;
	}

	boolean sanityCheck() {
		assert assertRepresentativeMapIsInjective();
		return true;
	}

	private static <E> boolean sanityCheckIntersectPartitionBlocks(final UnionFind<E> uf1, final UnionFind<E> uf2,
			final UnionFind<E> result, final HashRelation<E, E> uf1SplitInfo, final HashRelation<E, E> uf2SplitInfo) {
		/*
		 * check the split infos: each pair's lhs must be a representative in the corresponding input UnionFind, and the
		 * rhs must be a representative in the output UnionFind
		 */
		for (final E l : uf1SplitInfo.getDomain()) {
			if (uf1.find(l) != l) {
				assert false;
				return false;
			}
			for (final E r : uf1SplitInfo.getImage(l)) {
				if (result.find(r) != r) {
					assert false;
					return false;
				}
			}
		}
		for (final E l : uf2SplitInfo.getDomain()) {
			if (uf2.find(l) != l) {
				assert false;
				return false;
			}
			for (final E r : uf2SplitInfo.getImage(l)) {
				if (result.find(r) != r) {
					assert false;
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Asserts a class invariant: mRepresentatives must be injective, i.e., a representative cannot represent two
	 * equivalence classes
	 *
	 * @return
	 */
	private boolean assertRepresentativeMapIsInjective() {
		final Set<E> alreadySeenRepresentatives = new HashSet<>();
		for (final E rep : mRepresentative.values()) {
			assert !alreadySeenRepresentatives.contains(rep);
			alreadySeenRepresentatives.add(rep);
		}
		return true;
	}
}
