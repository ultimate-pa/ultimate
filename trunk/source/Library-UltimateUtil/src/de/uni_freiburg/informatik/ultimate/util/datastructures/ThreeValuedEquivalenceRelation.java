/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Memory efficient data structure that stores for a given equivalence relation if pairs are in the relation, not in the
 * relation, if the membership status is unknown.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <E>
 *            type of the elements in the equivalence relation
 */
public class ThreeValuedEquivalenceRelation<E> {

	private final UnionFind<E> mUnionFind;
	private final HashRelation<E, E> mDisequalities;
	private boolean mIsInconsistent;

	public ThreeValuedEquivalenceRelation() {
		mUnionFind = new UnionFind<>();
		mDisequalities = new HashRelation<>();
		mIsInconsistent = false;
	}

	public ThreeValuedEquivalenceRelation(final Comparator<E> elementComparator) {
		assert elementComparator != null : "use other constructor in this case!";
		mUnionFind = new UnionFind<>(elementComparator);
		mDisequalities = new HashRelation<>();
		mIsInconsistent = false;
	}

	public ThreeValuedEquivalenceRelation(final ThreeValuedEquivalenceRelation<E> tver) {
		this.mUnionFind = tver.mUnionFind.clone();
		this.mDisequalities = new HashRelation<>(tver.mDisequalities);
		this.mIsInconsistent = tver.mIsInconsistent;
		assert sanityCheck();
	}

	public ThreeValuedEquivalenceRelation(final UnionFind<E> newPartition, final HashRelation<E, E> newDisequalities) {
		mUnionFind = newPartition.clone();
		mDisequalities = new HashRelation<>(newDisequalities);
		mIsInconsistent = false;
		assert sanityCheck();
	}

	/**
	 * @return true iff elem was not contained in relation before (i.e. we made a change)
	 */
	public boolean addElement(final E elem) {
		if (mUnionFind.find(elem) == null) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
			return true;
		}
		return false;
	}

	/**
	 * Remove the given element (first argument) from this Tver.
	 *
	 * If elem is not the only element in its equivalence class and is the representative before removal,
	 *  we need to choose another representative, the second argument allows the caller to participate in that choice.
	 *
	 * @param elem
	 * @param newRepChoice if newRepChoice is non-null, and elem was representative before removal, newRepChoice will
	 *  be picked as new representative, otherwise this method picks some candidate (nondeterministically, depending on
	 *  the hashing order)
	 * @return the representative of elem's equivalence class after removal of elem, null if it was the only element of
	 *         its equivalence class
	 */
	public E removeElement(final E elem, final E newRepChoice) {
		assert newRepChoice == null || getRepresentative(elem) == getRepresentative(newRepChoice);
		final E rep = mUnionFind.find(elem);
		final Set<E> equivalenceClassCopy = new HashSet<>(mUnionFind.getEquivalenceClassMembers(elem));
		mUnionFind.remove(elem, newRepChoice);

		/*
		 * update mDistinctElements
		 */
		if (rep != elem) {
			// elem was not the representative of its equivalence class --> nothing to do for disequalities
			assert getRepresentative(rep) == rep;
			return rep;
		}
		// elem was the representative of its equivalence class --> we need to update mDistinctElements
		equivalenceClassCopy.remove(elem);
		if (equivalenceClassCopy.isEmpty()) {
			// elem was the only element in its equivalence class --> just remove it from disequalities
			mDisequalities.removeDomainElement(elem);
			mDisequalities.removeRangeElement(elem);
			assert sanityCheck();
			return null;
		}
		assert rep == elem;
		// elem was the representative of its equivalence class, but not the only element
		// --> replace it by the new representative in mDistinctElements
		final E newRep;
		if (newRepChoice == null) {
			newRep = mUnionFind.find(equivalenceClassCopy.iterator().next());
		} else {
			newRep = newRepChoice;
		}
		assert newRep!= null;
		mDisequalities.replaceDomainElement(elem, newRep);
		mDisequalities.replaceRangeElement(elem, newRep);
		assert sanityCheck();
		assert getRepresentative(newRep) == newRep : "the returned element must be a representative, "
				+ newRep + " is its own rep, but " +  getRepresentative(newRep) + " is.";
		return newRep;
	}

	/**
	 *
	 * @param elem1
	 * @param elem2
	 * @return true iff this data structure did not already store the equality of the specified pair
	 */
	public boolean reportEquality(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		final E oldRep1 = mUnionFind.find(elem1);
		if (oldRep1 == null) {
			throw new IllegalArgumentException("unknown element " + elem1);
		}
		final E oldRep2 = mUnionFind.find(elem2);
		if (oldRep2 == null) {
			throw new IllegalArgumentException("unknown element " + elem2);
		}

		if (oldRep1 == oldRep2) {
			// the elements already are in the same equivalence class, do nothing
			return false;
		}

		if (getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			reportInconsistency();
			return true;
		}

		mUnionFind.union(elem1, elem2);

		/*
		 * Because either oldRep1 or oldRep2 is no longer a representative now. By our convention, the element of the
		 * relation mDisequalities may only be representatives. Thus we may have to update mDisequalities accordingly.
		 */
		if (isRepresentative(oldRep1)) {
			// elem1 has kept its representative, elem2 has a new representative now
			assert mUnionFind.find(elem2) == oldRep1;

			mDisequalities.replaceDomainElement(oldRep2, oldRep1);
			mDisequalities.replaceRangeElement(oldRep2, oldRep1);
		} else {
			// elem2 has kept its representative, elem1 has a new representative now
			assert mUnionFind.find(elem1) == oldRep2;

			mDisequalities.replaceDomainElement(oldRep1, oldRep2);
			mDisequalities.replaceRangeElement(oldRep1, oldRep2);
		}
		assert sanityCheck();
		return true;
	}

	/**
	 * Sets the state of this TVER to "inconsistent".
	 */
	private void reportInconsistency() {
		mIsInconsistent = true;
	}

	/**
	 *
	 * @param elem1
	 * @param elem2
	 * @return true iff this data structure did not already store the disequality of the specified pair
	 */
	public boolean reportDisequality(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		final E rep1 = mUnionFind.find(elem1);
		if (rep1 == null) {
			throw new IllegalArgumentException("unknown element " + elem1);
		}
		final E rep2 = mUnionFind.find(elem2);
		if (rep2 == null) {
			throw new IllegalArgumentException("unknown element " + elem2);
		}

		if (getEqualityStatus(rep1, rep2) == EqualityStatus.NOT_EQUAL) {
			return false;
		}

		if (rep1 == rep2) {
			reportInconsistency();
			return true;
		}

		mDisequalities.addPair(rep1, rep2);
		assert sanityCheck();
		return true;
	}

	public E getRepresentativeAndAddElementIfNeeded(final E elem) {
		return mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
	}

	/**
	 * Returns the representative of the given element's equivalence class. Returns null if the given element has not
	 * been added yet.
	 *
	 * @param elem
	 *            element to get the representative for
	 * @return representative or null
	 */
	public E getRepresentative(final E elem) {
		return mUnionFind.find(elem);
	}

	public boolean isRepresentative(final E elem) {
		if (!getAllElements().contains(elem)) {
			throw new IllegalArgumentException("only call this for elements that are present!");
		}
		return getRepresentative(elem) == elem;
	}

	/**
	 * @return true iff the equalities and disequalities that have been reported are inconsistent
	 */
	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	public EqualityStatus getEqualityStatus(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException(
					"Cannot get equality status from inconsistent " + this.getClass().getSimpleName());
		}

		final E elem1Rep = mUnionFind.find(elem1);
		if (elem1Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem1);
		}
		final E elem2Rep = mUnionFind.find(elem2);
		if (elem2Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem2);
		}

		if (elem1Rep.equals(elem2Rep)) {
			return EqualityStatus.EQUAL;
		} else if (mDisequalities.containsPair(elem1Rep, elem2Rep) || mDisequalities.containsPair(elem2Rep, elem1Rep)) {
			return EqualityStatus.NOT_EQUAL;
		} else {
			return EqualityStatus.UNKNOWN;
		}
	}

	/**
	 *
	 * Note that this sanity check currently forbids null entries for the relation -- if we want null entries, we
	 * have to revise this.
	 *
	 * @return true iff sanity check is passed
	 */
	public boolean sanityCheck() {

		// call the sanityCheck of the underlying Unionfind
		if (!mUnionFind.sanityCheck()) {
			return false;
		}


		// mDisequalities may not contain null entries
		for (final Entry<E, E> en : mDisequalities.entrySet()) {
			if (en.getKey() == null) {
				return false;
			}
			if (en.getValue() == null) {
				return false;
			}
		}
		// disequalites only contain representatives
		for (final Entry<E, E> en : mDisequalities.entrySet()) {
			if (!isRepresentative(en.getKey())) {
				return false;
			}
			if (!isRepresentative(en.getValue())) {
				return false;
			}
		}
		return true;
	}

	public Collection<E> getAllRepresentatives() {
		return mUnionFind.getAllRepresentatives();
	}

	public Collection<Set<E>> getAllEquivalenceClasses() {
		return mUnionFind.getAllEquivalenceClasses();
	}

	/**
	 * Returns a String representation of this equivalence relation. Represents it by the partition and the list of
	 * disequalities. Exceptions:
	 * <li>If this is tautological (i.e. the partition only contains singletons and the set of disequalities is empty),
	 * this is represented by "True".
	 * <li>If this is inconsistent (i.e., the partition and the disequalities contradict), this is represented by
	 * "False".
	 */
	@Override
	public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("Equivalences: ");
		sb.append(mUnionFind);
		sb.append("\n");

		sb.append("Non-Equivalences: ");
		sb.append(mDisequalities);

		return sb.toString();
	}

	public Set<E> getAllElements() {
		return mUnionFind.getAllElements();
	}

	public Set<E> getRepresentativesUnequalTo(final E rep) {
		assert isRepresentative(rep);
		final Set<E> result = new HashSet<>();

		result.addAll(mDisequalities.getImage(rep));

		for (final E domEl : mDisequalities.getDomain()) {
			if (mDisequalities.getImage(domEl).contains(rep)) {
				result.add(domEl);
			}
		}

		return result;
	}

	/**
	 * @return Set of all elements that are known by this
	 *         {@link ThreeValuedEquivalenceRelation} and are equivalent to
	 *         <code>elem</code>.
	 */
	public Set<E> getEquivalenceClass(final E elem) {
		return mUnionFind.getEquivalenceClassMembers(elem);
	}

	public ThreeValuedEquivalenceRelation<E> join(final ThreeValuedEquivalenceRelation<E> other) {
		final UnionFind<E> newPartition =
				UnionFind.intersectPartitionBlocks(this.mUnionFind, other.mUnionFind).getFirst();
		return new ThreeValuedEquivalenceRelation<>(newPartition, xJoinDisequalities(this, other, newPartition, true));
	}

	public ThreeValuedEquivalenceRelation<E> meet(final ThreeValuedEquivalenceRelation<E> other) {
		final UnionFind<E> newPartition = UnionFind.unionPartitionBlocks(this.mUnionFind, other.mUnionFind);
		return new ThreeValuedEquivalenceRelation<>(newPartition, xJoinDisequalities(this, other, newPartition, false));
	}

	public Triple<UnionFind<E>, HashRelation<E, E>, HashRelation<E, E>> joinPartitions(
			final ThreeValuedEquivalenceRelation<E> other) {
		return UnionFind.intersectPartitionBlocks(this.mUnionFind, other.mUnionFind);
	}

	/**
	 * Conjoin or disjoin two disequality relations.
	 *
	 * @param tver1
	 * @param tver2
	 * @param newElemPartition
	 * @param conjoin
	 *            conjoin or disjoin?
	 * @return
	 */
	private static <E> HashRelation<E, E> xJoinDisequalities(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2, final UnionFind<E> newElemPartition, final boolean conjoin) {
		final HashRelation<E, E> result = new HashRelation<>();
		for (final Entry<E, E> pair : CrossProducts
				.binarySelectiveCrossProduct(newElemPartition.getAllRepresentatives(), false, false)) {
			final boolean addDisequality;
			if (conjoin) {
				addDisequality = tver1.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL
						&& tver2.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL;
			} else {
				addDisequality = tver1.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL
						|| tver2.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL;
			}
			if (addDisequality) {
				result.addPair(pair.getKey(), pair.getValue());
			}
		}
		return result;
	}

	public Map<E, E> getSupportingEqualities() {
		final Map<E, E> result = new HashMap<>();
		for (final Set<E> eqc : mUnionFind.getAllEquivalenceClasses()) {
			E lastElement = null;
			;
			for (final E e : eqc) {
				if (lastElement != null) {
					result.put(e, lastElement);
				}
				lastElement = e;
			}
		}
		return result;
	}

	public HashRelation<E, E> getDisequalities() {
		assert !mDisequalities.entrySet().stream().anyMatch(pr -> pr.getValue() == null);
		// TODO: make a copy before returning or not? (safer but slower)
		return new HashRelation<>(mDisequalities);
	}

	/**
	 *
	 * @return true iff the equality relation represented by this constraint is empty, i.e., for any two elements e1, e2
	 *         getEqualityStatus(e1, e2) returns UNKNOWN.
	 */
	public boolean isTautological() {
		return getSupportingEqualities().isEmpty() && mDisequalities.isEmpty();
	}

	public void transformElements(final Function<E, E> transformer) {
		mUnionFind.transformElements(transformer);

		final HashRelation<E, E> disequalitiesCopy = new HashRelation<>(mDisequalities);
		for (final Entry<E, E> pair : disequalitiesCopy) {
			mDisequalities.removePair(pair.getKey(), pair.getValue());
			mDisequalities.addPair(transformer.apply(pair.getKey()), transformer.apply(pair.getValue()));
		}
		assert sanityCheck();
	}

	/**
	 * Computes a ThreeValuedEquivalenceRelation that has the same constraints as this except some are filtered out.
	 * In Particular only constraints are kept where on at least one side an element from the given set elems occurs.
	 * (if we think of this TVER as two sets pairs, equalities and disequalities)
	 * The elements that become unconstrained through this are omitted from the result.
	 *
	 * Example, in the partition view:
	 * elems {q1, q2}
	 * this: {q1, a, b}, {d, e, f}, {q2}, q1 != e
	 * result: {q1, a, b}, {q2}, q1 != e
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @param elem element constraints over which are to be kept
	 * @return a new, projected ThreeValuedEquivalenceRelation
	 */
	public ThreeValuedEquivalenceRelation<E> filterAndKeepOnlyConstraintsThatIntersectWith(final Set<E> elems) {
		final UnionFind<E> newUf = mUnionFind.getElementComparator() != null
				? new UnionFind<>(mUnionFind.getElementComparator()) : new UnionFind<>();
		for (final E elem : elems) {
			if (newUf.find(elem) != null) {
				// already constructed current elem's equivalence class
				continue;
			}
			if (mUnionFind.find(elem) == null) {
				// the current elem has never been added to this TVER; don't add it to the new TVER either
				continue;
			}
			final Set<E> elemEqc = new HashSet<>(mUnionFind.getEquivalenceClassMembers(elem));
			// retain representatives because otherwise we have to do extra work for literal set constraints
			newUf.addEquivalenceClass(elemEqc, mUnionFind.find(elem));
//			newUf.addEquivalenceClass(elemEqc);
		}
		final HashRelation<E, E> newDisequalities = new HashRelation<>();
		for (final Entry<E, E> deq : mDisequalities.entrySet()) {
//			if (elems.contains(deq.getKey()) || elems.contains(deq.getValue())) {
			if (DataStructureUtils.getSomeCommonElement(getEquivalenceClass(deq.getKey()), elems).isPresent()
				|| DataStructureUtils.getSomeCommonElement(getEquivalenceClass(deq.getValue()), elems).isPresent()) {
				newDisequalities.addPair(newUf.findAndConstructEquivalenceClassIfNeeded(deq.getKey()),
						newUf.findAndConstructEquivalenceClassIfNeeded(deq.getValue()));
			}
		}
		return new ThreeValuedEquivalenceRelation<>(newUf, newDisequalities);
	}


	/**
	 * Constructs a new {@link ThreeValuedEquivalenceRelation} that is similar to
	 * this but restricted to contraints where both elements occur in the set
	 * elems.
	 */
	public ThreeValuedEquivalenceRelation<E> projectTo(final Set<E> elems) {
		final UnionFind<E> newUf = mUnionFind.getElementComparator() != null ?
				new UnionFind<>(mUnionFind.getElementComparator()) :
					new UnionFind<>();
		for (final E elem : elems) {
			if (newUf.find(elem) != null) {
				// already constructed current elem's equivalence class
				continue;
			}
			if (mUnionFind.find(elem) == null) {
				// the current elem has never been added to this TVER; don't add it to the new TVER either
				continue;
			}
			final Set<E> elemEqc = mUnionFind.getEquivalenceClassMembers(elem);
			newUf.addEquivalenceClass(DataStructureUtils.intersection(elemEqc, elems));
		}
		final HashRelation<E, E> newDisequalities = new HashRelation<>();
		for (final Entry<E, E> deq : mDisequalities.entrySet()) {
			final Optional<E> lhsRep = DataStructureUtils.getSomeCommonElement(elems, getEquivalenceClass(deq.getKey()));
			if (lhsRep.isPresent()) {
				final Optional<E> rhsRep = DataStructureUtils.getSomeCommonElement(elems, getEquivalenceClass(deq.getValue()));
				if (rhsRep.isPresent()) {
					newDisequalities.addPair(newUf.find(lhsRep.get()),
							newUf.find(rhsRep.get()));
				}
			}
		}
		return new ThreeValuedEquivalenceRelation<>(newUf, newDisequalities);
	}



	/**
	 * We call an element constrained iff this TVER puts any non-tautological constraint on it. In particular, the
	 * element e is constrained if both of the following conditions hold
	 * <li>e is the only member of its equivalence class
	 * <li>e does not appear in a disequality
	 *
	 * @param elem
	 *            the element to check
	 * @return true iff elem is constrained by this
	 */
	public boolean isConstrained(final E elem) {
		if (mUnionFind.find(elem) == null) {
			throw new IllegalArgumentException();
		}
		if (getEquivalenceClass(elem).size() > 1) {
			return true;
		}
		if (mDisequalities.getImage(elem).size() > 0) {
			return true;
		}
		for (final Entry<E, E> en : mDisequalities.entrySet()) {
			if (en.getValue().equals(elem)) {
				return true;
			}
		}
		return false;
	}

	public void removeDisequality(final E elem1, final E elem2) {
		mDisequalities.removePair(elem1, elem2);
		mDisequalities.removePair(elem2, elem1);
	}
}
