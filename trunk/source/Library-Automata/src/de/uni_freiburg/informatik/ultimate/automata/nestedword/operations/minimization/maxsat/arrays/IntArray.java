/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>
 *
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.Arrays;
import java.util.Iterator;

/**
 * Int array with get, set, add, and clear operations which is implemented using a native int[] array for efficiency.
 * This is crucial if millions of integers should be stored, because storing these as
 * <code>ArrayList&lt;Integer&gt;</code> is too much for the GC.
 *
 * @author stimpflj
 */
final class IntArray implements Iterable<Integer> {

	private int[] mArray;
	private int mSize;
	private int mCapacity;

	IntArray() {
		mArray = new int[0];
		mSize = 0;
		mCapacity = 0;
	}

	int get(final int idx) {
		if (idx < 0 || idx >= mSize) {
			throw new ArrayIndexOutOfBoundsException();
		}

		return mArray[idx];
	}

	void set(final int idx, final int val) {
		if (idx < 0 || idx >= mSize) {
			throw new ArrayIndexOutOfBoundsException();
		}

		mArray[idx] = val;
	}

	void add(final int val) {
		if (mSize == mCapacity) {
			final int newCapacity = (mCapacity == 0) ? 4 : 2 * mCapacity;
			mArray = Arrays.copyOf(mArray, newCapacity);
			mCapacity = newCapacity;
		}

		mArray[mSize++] = val;
	}

	void clear() {
		mArray = new int[0];
		mSize = 0;
		mCapacity = 0;
	}

	int size() {
		return mSize;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null || !(obj instanceof IntArray)) {
			return false;
		}

		final IntArray b = (IntArray) obj;

		if (b.mSize != mSize) {
			return false;
		}

		for (int i = 0; i < mSize; i++) {
			if (b.mArray[i] != mArray[i]) {
				return false;
			}
		}

		return true;
	}

	@Override
	public int hashCode() {
		throw new UnsupportedOperationException("hashCode() not implemented");
	}

	@Override
	public Iterator<Integer> iterator() {
		return new IntArrayIterator(mArray, 0, mSize);
	}

	private static final class IntArrayIterator implements Iterator<Integer> {
		private final int[] mInnerArray;
		private final int mLast;
		private int mIdx;

		IntArrayIterator(final int[] array, final int first, final int last) {
			assert 0 <= first && first <= last && last <= array.length;

			mInnerArray = array;
			mLast = last;
			mIdx = first;
		}

		@Override
		public boolean hasNext() {
			return mIdx < mLast;
		}

		@Override
		public Integer next() {
			if (mIdx == mLast) {
				throw new ArrayIndexOutOfBoundsException();
			}

			return mInnerArray[mIdx++];
		}
	}
}
