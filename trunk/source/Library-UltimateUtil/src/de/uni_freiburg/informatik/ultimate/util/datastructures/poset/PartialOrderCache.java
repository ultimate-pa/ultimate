/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class PartialOrderCache<E> {

	private final IPartialComparator<E> mComparator;

	private final HashRelation<E, E> mStrictlySmaller;
	private final UnionFind<E> mEquivalences;

	private final Set<E> mMaximalElements;
//	private final Set<E> mMinimalElements;



	public PartialOrderCache(final IPartialComparator<E> comparator) {
		mComparator = comparator;
		mStrictlySmaller = new HashRelation<>();
		mEquivalences = new UnionFind<>();
		mMaximalElements = new HashSet<>();
//		mMinimalElements = new HashSet<>();
	}

	public E addElement(final E elemToAdd) {
		E rep = mEquivalences.find(elemToAdd);
		if (rep != null) {
			// we already know this element, return the representative
			return rep;
		}
		// elemToAdd element is new
		rep = mEquivalences.findAndConstructEquivalenceClassIfNeeded(elemToAdd);
		assert rep == elemToAdd;
//		mMinimalElements.add(rep);
		mMaximalElements.add(rep);

		for (final E otherRep : new ArrayList<>(mEquivalences.getAllRepresentatives())) {
			if (otherRep == rep) {
				// nothing to do
				continue;
			}
			switch (mComparator.compare(elemToAdd, otherRep)) {
			case EQUAL:
				mEquivalences.union(rep, otherRep);
				final E newRep = mEquivalences.find(rep);
				if (newRep == rep) {
					// representative has changed
					assert mEquivalences.find(otherRep) == rep;
//					mMinimalElements.remove(otherRep);
					mMaximalElements.remove(otherRep);
					mStrictlySmaller.replaceDomainElement(otherRep, newRep);
					mStrictlySmaller.replaceRangeElement(otherRep, newRep);
				} else {
					// representative is the old one but we have already made some entries into the data structures
//					mMinimalElements.remove(rep);
					mMaximalElements.remove(rep);
					mStrictlySmaller.replaceDomainElement(rep, newRep);
					mStrictlySmaller.replaceRangeElement(rep, newRep);
				}
				assert sanityCheck();
				return newRep;
			case STRICTLY_SMALLER:
				addStrictlySmaller(elemToAdd, otherRep);
				break;
			case STRICTLY_GREATER:
				addStrictlySmaller(otherRep, elemToAdd);
				break;
			case INCOMPARABLE:
				break;
			}
		}

		assert sanityCheck();
		return rep;
	}

	private void addStrictlySmaller(final E smaller, final E greater) {
		assert mEquivalences.find(smaller) == smaller;
		assert mEquivalences.find(greater) == greater;

		final E smallerRep = mEquivalences.find(smaller);
		final E greaterRep = mEquivalences.find(greater);

		mStrictlySmaller.addPair(smallerRep, greaterRep);
		assert assertStrictlySmaller(smallerRep, greaterRep);
//		mExplies.addPair(greaterRep, smallerRep);

//		mMinimalElements.remove(greaterRep);
		mMaximalElements.remove(smallerRep);

		assert sanityCheck();
	}

	public boolean lowerEqual(final E elem1, final E elem2) {
		if (elem1 == elem2) {
			return true;
		}
		assert sanityCheck();
		final E rep1 = addElement(elem1);
		final E rep2 = addElement(elem2);
		if (rep1 == rep2) {
			// elements are equal
			return true;
		}
		/*
		 * elements are not equal
		 * We need to test if there is a path through the graph mStrictlySmaller from rep1 to rep2.
		 */
		return strictlySmaller(rep1, rep2);
	}

	protected boolean strictlySmaller(final E rep1, final E rep2) {
		if (mStrictlySmaller.containsPair(rep1, rep2)) {
			return true;
		}
		final Deque<E> worklist = new ArrayDeque<>();
		worklist.add(rep1);
		while (!worklist.isEmpty()) {
			final E current = worklist.pop();

			if (current == rep2 && current != rep1) {
				/*
				 * found a path
				 * update the map (caching the transitive closure information)
				 * return true
				 */
				mStrictlySmaller.addPair(rep1, rep2);
				assert assertStrictlySmaller(rep1, rep2);
				assert sanityCheck();
				return true;
			}
			worklist.addAll(mStrictlySmaller.getImage(current));
		}
		// found no path --> not smaller
		return false;
	}

	public boolean greaterEqual(final E elem1, final E elem2) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	/**
	 * Get the maximal elements from to the given list (or elements equivalent to those)
	 *
	 * @param elements
	 * @return
	 */
	public Set<E> getMaximalRepresentatives(final Collection<E> elements) {
		final Set<E> reps = new HashSet<>();
		for (final E el : elements) {
			reps.add(addElement(el));
		}

		final Set<E> result = new HashSet<>(reps);

		for (final E rep1 : reps) {
			for (final E rep2 : reps) {
				if (strictlySmaller(rep1, rep2)) {
					result.remove(rep1);
				}
			}
		}

		return result;
	}

	/**
	 * Get overall maximal elements in the map (modulo being equal/only representatives)
	 *
	 * @return
	 */
	public Set<E> getMaximalRepresentatives() {
		return mMaximalElements;
	}

//	public Set<E> getMinimalRepresentatives() {
//		return mMinimalElements;
//	}

	boolean assertStrictlySmaller(final E elem1, final E elem2) {
		// order must be correct
		if (mComparator.compare(elem1, elem2) != ComparisonResult.STRICTLY_SMALLER) {
			final ComparisonResult compres = mComparator.compare(elem1, elem2);
			assert false;
			return false;
		}
		return true;
	}

	boolean sanityCheck() {
		/*
		 * the sets mMinimalElemnts and mMaximalElements may only contain representatives
		 */
//		for (final E e : mMinimalElements) {
//			if (mEquivalences.find(e) != e) {
//				final E find = mEquivalences.find(e);
//				assert false;
//				return false;
//			}
//		}
		for (final E e : mMaximalElements) {
			if (mEquivalences.find(e) != e) {
				final E find = mEquivalences.find(e);
				assert false;
				return false;
			}
		}

		for (final Entry<E, E> en : mStrictlySmaller) {
			// key must be a representative
			if (mEquivalences.find(en.getKey()) != en.getKey()) {
				final E find = mEquivalences.find(en.getKey());
				assert false;
				return false;
			}
			// value must be a representative
			if (mEquivalences.find(en.getValue()) != en.getValue()) {
				final E find = mEquivalences.find(en.getValue());
				assert false;
				return false;
			}

		}


		return true;
	}





}
