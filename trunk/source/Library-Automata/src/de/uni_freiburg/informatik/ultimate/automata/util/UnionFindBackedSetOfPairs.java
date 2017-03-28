/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.util;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs.PartitionSizeInformation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Partition implementation of a set of pairs that uses {@link UnionFind}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class UnionFindBackedSetOfPairs<E> implements ISetOfPairs<E, Collection<Set<E>>> {
	private final UnionFind<E> mUnionFind;
	/**
	 * Partition that is returned as result. Constructed on-demand. Once constructed we cannot add new elements.
	 */
	private Collection<Set<E>> mPartition;
	private PartitionSizeInformation mPartitionSizeInformation;

	/**
	 * Constructor.
	 */
	public UnionFindBackedSetOfPairs() {
		mUnionFind = new UnionFind<>();
	}

	/**
	 * Note: Two calls to this method result in different {@link Pair} objects.
	 * <p>
	 * {@inheritDoc}
	 */
	@Override
	public Iterator<Pair<E, E>> iterator() {
		if (mPartition == null) {
			mPartition = mUnionFind.getAllEquivalenceClasses();
		}
		final Iterator<Set<E>> iterator = mPartition.iterator();
		if (iterator.hasNext()) {
			return new PartitionBackedSetOfPairs.IteratorFromPartition<>(iterator);
		}
		return Collections.emptyIterator();
	}

	@Override
	public void addPair(final E lhs, final E rhs) {
		if (mPartition == null) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(lhs);
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(rhs);
			mUnionFind.union(lhs, rhs);
		} else {
			throw new IllegalStateException("final partition already constructed, unable to add new pairs");
		}

	}

	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		// in same equivalence class if both have same representative
		final E lhsRepresentative = mUnionFind.find(lhs);
		final E rhsRepresentative = mUnionFind.find(rhs);
		return lhsRepresentative.equals(rhsRepresentative);
	}

	@Override
	public Collection<Set<E>> getRelation() {
		if (mPartition == null) {
			mPartition = mUnionFind.getAllEquivalenceClasses();
		}
		return mPartition;
	}

	/**
	 * @return Size information of the partition.
	 */
	public PartitionSizeInformation getOrConstructPartitionSizeInformation() {
		if (mPartition == null) {
			mPartition = mUnionFind.getAllEquivalenceClasses();
		}
		if (mPartitionSizeInformation == null) {
			mPartitionSizeInformation = new PartitionSizeInformation(mPartition);
		}
		return mPartitionSizeInformation;
	}

	@Override
	public String toString() {
		return mUnionFind.toString();
	}

	@Deprecated
	public UnionFind<E> getUnionFind() {
		return mUnionFind;
	}

}
