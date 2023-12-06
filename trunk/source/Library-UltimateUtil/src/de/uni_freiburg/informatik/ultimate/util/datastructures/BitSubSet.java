/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

import java.util.AbstractCollection;
import java.util.BitSet;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.LazyInt;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

/**
 * A data structure that efficiently represents (immutable) subsets of a given set, using bit vectors ({@link BitSet}).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <E>
 *            The type of elements in the set.
 */
public final class BitSubSet<E> extends AbstractCollection<E> {
	private final Factory<E> mFactory;
	private final BitSet mBitSet;
	private final LazyInt mHash;

	private BitSubSet(final Factory<E> factory, final BitSet bitset) {
		mFactory = factory;
		mBitSet = bitset;
		mHash = new LazyInt(mBitSet::hashCode);
	}

	@Override
	public boolean contains(final Object o) {
		final Integer index = mFactory.getIndex(o);
		return index != null && mBitSet.get(index);
	}

	public boolean containsAll(final BitSubSet<?> c) {
		assert c.mFactory == mFactory : "Cannot compare sets from different universes";

		final BitSet diff = BitSet.valueOf(c.mBitSet.toLongArray());
		diff.andNot(mBitSet);
		return diff.isEmpty();
	}

	@Override
	public Iterator<E> iterator() {
		return new BitSubSetIterator<>(mFactory.mElements, mBitSet);
	}

	@Override
	public int size() {
		return mBitSet.cardinality();
	}

	@Override
	public boolean isEmpty() {
		return mBitSet.isEmpty();
	}

	@Override
	public int hashCode() {
		return mHash.get();
	}

	@Override
	public boolean equals(final Object o) {
		if (this == o) {
			return true;
		}
		if (o instanceof BitSubSet<?>) {
			final BitSubSet<?> b = (BitSubSet<?>) o;
			if (b.mFactory == mFactory) {
				return b.mBitSet.equals(mBitSet);
			}
		}
		return super.equals(o);
	}

	private static class BitSubSetIterator<E> implements Iterator<E> {
		private final Object[] mElements;
		private final BitSet mBitSet;
		private int mIndex;

		public BitSubSetIterator(final Object[] elements, final BitSet bitset) {
			mElements = elements;
			mBitSet = bitset;
			mIndex = mBitSet.nextSetBit(0);
		}

		@Override
		public boolean hasNext() {
			return mIndex >= 0;
		}

		@Override
		public E next() {
			if (!hasNext()) {
				throw new NoSuchElementException();
			}

			final E elem = (E) mElements[mIndex];
			mIndex = mBitSet.nextSetBit(mIndex + 1);

			return elem;
		}
	}

	/**
	 * A factory to create {@link BitSubSet} instances representing subsets of a shared universe.
	 *
	 * This class also implements an {@link ILattice} for the created instances.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <E>
	 *            The type of elements in the universe
	 */
	public static class Factory<E> implements ILattice<BitSubSet<E>> {

		private static final String LEFT_NOT_CREATED_BY_FACTORY = "Operand 'left' not created by this factory";
		private static final String RIGHT_NOT_CREATED_BY_FACTORY = "Operand 'right' not created by this factory";

		private final Object[] mElements;
		private final Map<E, Integer> mIndexMap;

		private BitSubSet<E> mUniverse;
		private BitSubSet<E> mEmpty;

		/**
		 * Create a new factory capable of creating subsets of the given universe set.
		 *
		 * @param universe
		 *            The set of all elements that can appear in the created subsets.
		 */
		public Factory(final Set<E> universe) {
			mElements = universe.stream().sorted(Comparator.comparing(Objects::hashCode)).toArray();
			mIndexMap = new HashMap<>(universe.size());

			for (int i = 0; i < mElements.length; ++i) {
				mIndexMap.put((E) mElements[i], i);
			}
		}

		/**
		 * Turn an ordinary {@link Set} instance into a {@link BitSubSet}.
		 *
		 * This is only allowed if the set contains only elements in this instance's {@link #universe()}. Otherwise the
		 * operation will fail.
		 *
		 * @param set
		 *            The set to be converted into a {@link BitSubSet}
		 * @return an equivalent {@link BitSubSet}, i.e., a set such that {@link Set#equals(Object)} will return true
		 *         when given the original set
		 */
		public BitSubSet<E> valueOf(final Set<E> set) {
			final BitSet bitset = new BitSet(mElements.length);
			for (final E elem : set) {
				final int index = getIndex(elem);
				bitset.set(index);
			}
			return new BitSubSet<>(this, bitset);
		}

		/**
		 * @return The set of all elements in this instance's universe
		 */
		public BitSubSet<E> universe() {
			if (mUniverse == null) {
				final BitSet bitset = new BitSet(mElements.length);
				flip(bitset);
				mUniverse = new BitSubSet<>(this, bitset);
			}
			return mUniverse;
		}

		/**
		 * @return a representation of the empty set
		 */
		public BitSubSet<E> empty() {
			if (mEmpty == null) {
				mEmpty = new BitSubSet<>(this, new BitSet());
			}
			return mEmpty;
		}

		/**
		 * @param operand
		 *            A set created by this instance
		 * @return The given set's complement relative to the {@link #universe()}.
		 */
		public BitSubSet<E> complement(final BitSubSet<E> operand) {
			assert operand.mFactory == this : "operand not created by this factory";

			final BitSet bitset = copy(operand.mBitSet);
			flip(bitset);
			return new BitSubSet<>(this, bitset);
		}

		/**
		 * @param left
		 *            A set created by this instance
		 * @param right
		 *            A set created by this instance
		 * @return A set representing the union of the given sets
		 */
		public BitSubSet<E> union(final BitSubSet<E> left, final BitSubSet<E> right) {
			assert left.mFactory == this : LEFT_NOT_CREATED_BY_FACTORY;
			assert right.mFactory == this : RIGHT_NOT_CREATED_BY_FACTORY;

			if (left == right) {
				return left;
			}
			if (right.isEmpty()) {
				return left;
			}
			if (left.isEmpty()) {
				return right;
			}
			final BitSet union = copy(left.mBitSet);
			union.or(right.mBitSet);
			return new BitSubSet<>(this, union);
		}

		/**
		 * @param left
		 *            A set created by this instance
		 * @param right
		 *            A set created by this instance
		 * @return A set representing the intersection of the given sets
		 */
		public BitSubSet<E> intersection(final BitSubSet<E> left, final BitSubSet<E> right) {
			assert left.mFactory == this : LEFT_NOT_CREATED_BY_FACTORY;
			assert right.mFactory == this : RIGHT_NOT_CREATED_BY_FACTORY;

			if (left == right) {
				return left;
			}
			if (right.isEmpty()) {
				return empty();
			}
			if (left.isEmpty()) {
				return empty();
			}
			final BitSet inter = copy(left.mBitSet);
			inter.and(right.mBitSet);
			return new BitSubSet<>(this, inter);
		}

		/**
		 * @param left
		 *            A set created by this instance
		 * @param right
		 *            A set created by this instance
		 * @return A set representing the difference of the given sets
		 */
		public BitSubSet<E> difference(final BitSubSet<E> left, final BitSubSet<E> right) {
			assert left.mFactory == this : LEFT_NOT_CREATED_BY_FACTORY;
			assert right.mFactory == this : RIGHT_NOT_CREATED_BY_FACTORY;

			if (left.isEmpty() || right.isEmpty()) {
				return left;
			}
			final BitSet diff = copy(left.mBitSet);
			diff.andNot(right.mBitSet);
			return new BitSubSet<>(this, diff);
		}

		private void flip(final BitSet bitset) {
			if (mElements.length == 0) {
				return;
			}
			bitset.flip(0, mElements.length);
		}

		private static BitSet copy(final BitSet bitset) {
			return (BitSet) bitset.clone();
		}

		private final Integer getIndex(final Object element) {
			return mIndexMap.get(element);
		}

		@Override
		public ComparisonResult compare(final BitSubSet<E> o1, final BitSubSet<E> o2) {
			assert o1.mFactory == this && o2.mFactory == this : "operand not created by this factory";
			if (o1.equals(o2)) {
				return ComparisonResult.EQUAL;
			}
			if (o2.containsAll(o1)) {
				return ComparisonResult.STRICTLY_SMALLER;
			}
			if (o1.containsAll(o2)) {
				return ComparisonResult.STRICTLY_GREATER;
			}
			return ComparisonResult.INCOMPARABLE;
		}

		@Override
		public BitSubSet<E> getBottom() {
			return empty();
		}

		@Override
		public BitSubSet<E> getTop() {
			return universe();
		}

		@Override
		public BitSubSet<E> supremum(final BitSubSet<E> h1, final BitSubSet<E> h2) {
			return union(h1, h2);
		}

		@Override
		public BitSubSet<E> infimum(final BitSubSet<E> h1, final BitSubSet<E> h2) {
			return intersection(h1, h2);
		}
	}
}
