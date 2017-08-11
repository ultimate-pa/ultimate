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

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Memory efficient data structure that stores for a given equivalence relation
 * if pairs are in the relation, not in the relation, if the membership status
 * is unknown
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ThreeValuedEquivalenceRelation<E> {
	
	private final UnionFind<E> mUnionFind;
	private final HashRelation<E, E> mDistinctElements;
	private boolean mContainsContradiction;
	
	public ThreeValuedEquivalenceRelation() {
		mUnionFind = new UnionFind<>();
		mDistinctElements = new HashRelation<>();
		mContainsContradiction = false;
	}
	
	public ThreeValuedEquivalenceRelation(final ThreeValuedEquivalenceRelation<E> tver) {
		this.mUnionFind = new UnionFind<>(tver.mUnionFind);
		this.mDistinctElements = new HashRelation<>(tver.mDistinctElements);
		this.mContainsContradiction = tver.mContainsContradiction;
	}
	
	/**
	 * @return true iff elem was not contained in relation before
	 */
	public boolean addElement(final E elem) {
		final E rep = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
		return (rep != elem);
	}
	
	public void reportEquality(final E elem1, final E elem2) {
		assert !mContainsContradiction : "already in an inconsistent state, check for contradiction before calling "
				+ "this";

		final E oldRep1 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem1);
		final E oldRep2 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem2);
		
		if (getEquality(elem1, elem2) == Equality.NOT_EQUAL) {
			mContainsContradiction = true;
			return;
		}

		mUnionFind.union(elem1, elem2);
		
		// we need to update the disequalities such that they still only talk about representatives
		if (isRepresentative(oldRep1)) {
			// elem1 has kept its representative, elem2 has a new representative now 
			assert mUnionFind.find(elem2) == oldRep1;
			
			mDistinctElements.replaceRangeElement(oldRep2, oldRep1);
			mDistinctElements.replaceDomainElement(oldRep2, oldRep1);
		} else {
			// elem2 has kept its representative, elem1 has a new representative now 
			assert mUnionFind.find(elem1) == oldRep2;
			
			mDistinctElements.replaceRangeElement(oldRep1, oldRep2);
			mDistinctElements.replaceDomainElement(oldRep1, oldRep2);
		}
	}
	
	public void reportNotEquals(final E elem1, final E elem2) {
		assert !mContainsContradiction : "already in an inconsistent state, check for contradiction before calling "
				+ "this";

		final E rep1 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem1);
		final E rep2 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem2);

		if (rep1 == rep2) {
			mContainsContradiction = true;
			return;
		}
		
		mDistinctElements.addPair(rep1, rep2);
	}
	
	public E getRepresentative(final E elem) {
		return mUnionFind.find(elem);
	}
	
	public boolean isRepresentative(final E elem) {
		return getRepresentative(elem) == elem;
	}
	
	/**
	 * @return true iff the equalities and disequaleties that have been reported contain a contradiction
	 */
	public boolean containsContradiction() {
		return mContainsContradiction;
	}
	
	public Equality getEquality(final E elem1, final E elem2) {
		assert !mContainsContradiction : "check for contradiction before calling this";
		
		final E elem1Rep = mUnionFind.find(elem1);
		if (elem1Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem1);
		}
		final E elem2Rep = mUnionFind.find(elem2);
		if (elem2Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem2);
		}
		
		if (elem1Rep.equals(elem2Rep)) {
			return Equality.EQUAL;
		} else if (mDistinctElements.containsPair(elem1Rep, elem2Rep) 
				|| mDistinctElements.containsPair(elem2Rep, elem1Rep)) {
			return Equality.NOT_EQUAL;
		} else {
			return Equality.UNKNOWN;
		}
	}
}

