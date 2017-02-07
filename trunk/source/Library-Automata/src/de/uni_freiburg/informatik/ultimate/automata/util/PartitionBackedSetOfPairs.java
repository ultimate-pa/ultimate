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

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Partition implementation of a set of pairs.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class PartitionBackedSetOfPairs<E> implements ISetOfPairs<E, Collection<Set<E>>> {
	protected final Collection<Set<E>> mPartition;
	
	/**
	 * @param partition
	 *            Partition.
	 */
	public PartitionBackedSetOfPairs(final Collection<Set<E>> partition) {
		mPartition = partition;
	}
	
	@Override
	public Iterator<Pair<E, E>> iterator() {
		final Iterator<Set<E>> iterator = mPartition.iterator();
		if (iterator.hasNext()) {
			return new IteratorFromPartition(iterator);
		}
		return Collections.emptyIterator();
	}
	
	@Override
	public void addPair(final E lhs, final E rhs) {
		throw new UnsupportedOperationException("The partition must be specified at construction time.");
	}
	
	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		throw new UnsupportedOperationException("This class does not support a contains() method. Use the "
				+ PartitionAndMapBackedSetOfPairs.class.getSimpleName() + " class instead.");
	}
	
	@Override
	public Collection<Set<E>> getRelation() {
		return mPartition;
	}
	
	/**
	 * Iterator wrapper.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	// false-positive warnings
	@SuppressWarnings({ "findbugs:UUF_UNUSED_FIELD", "findbugs:UWF_UNWRITTEN_FIELD" })
	protected final class IteratorFromPartition implements Iterator<Pair<E, E>> {
		private final Iterator<Set<E>> mBlockIt;
		private Iterator<E> mElemLhsIt;
		private Iterator<E> mElemRhsIt;
		private Iterable<E> mBlock;
		private E mElemLhs;
		
		public IteratorFromPartition(final Iterator<Set<E>> blockIterator) {
			mBlockIt = blockIterator;
			advanceToNextBlock();
		}
		
		@Override
		public boolean hasNext() {
			if (mElemRhsIt.hasNext()) {
				return true;
			}
			if (mElemLhsIt.hasNext()) {
				mElemLhs = mElemLhsIt.next();
				mElemRhsIt = mBlock.iterator();
				return true;
			}
			if (mBlockIt.hasNext()) {
				advanceToNextBlock();
				return true;
			}
			return false;
		}
		
		@Override
		public Pair<E, E> next() {
			final E rhs = mElemRhsIt.next();
			return new Pair<>(mElemLhs, rhs);
		}
		
		private void advanceToNextBlock() {
			mBlock = mBlockIt.next();
			mElemLhsIt = mBlock.iterator();
			mElemRhsIt = mBlock.iterator();
		}
	}
}
