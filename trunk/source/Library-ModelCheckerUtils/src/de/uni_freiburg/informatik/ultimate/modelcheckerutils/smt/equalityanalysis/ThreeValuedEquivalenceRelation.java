/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult.Equality;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
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
	
	public ThreeValuedEquivalenceRelation() {
		mUnionFind = new UnionFind<>();
		mDistinctElements = new HashRelation<>();
	}
	
	public ThreeValuedEquivalenceRelation(final ThreeValuedEquivalenceRelation<E> tver) {
		this.mUnionFind = new UnionFind<>(tver.mUnionFind);
		this.mDistinctElements = new HashRelation<>(tver.mDistinctElements);
	}
	
	
	/**
	 * @return true iff elem was not contained in relation before
	 */
	public boolean addElement(final E elem) {
		final E rep = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
		return (rep != elem);
	}
	
	public void reportEquality(final E elem1, final E elem2) {
		mUnionFind.union(elem1, elem2);
	}
	
	public void reportNotEquals(final E elem1, final E elem2) {
		mDistinctElements.addPair(elem1, elem2);
	}
	
	public E getRepresentative(final E elem) {
		return mUnionFind.find(elem);
	}
	
	public boolean isRepresentative(final E elem) {
		return getRepresentative(elem) == elem;
	}
	
	public Equality getEquality(final E elem1, final E elem2) {
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
		} else if (mDistinctElements.containsPair(elem1, elem2) || mDistinctElements.containsPair(elem2, elem1)) {
			return Equality.NOT_EQUAL;
		} else {
			return Equality.UNKNOWN;
		}
	}
	
	
}

