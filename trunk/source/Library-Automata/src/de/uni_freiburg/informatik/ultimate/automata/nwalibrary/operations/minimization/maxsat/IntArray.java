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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.Arrays;
import java.util.Iterator;

/**
 * Int array with get, set, add, and clear operations which is implemented using
 * a native int[] array for efficiency. This is crucial if millions of integers
 * should be stored, because storing these as
 * <code>ArrayList&lt;Integer&gt;</code> is too much for the GC.
 *
 * @author stimpflj
 *
 */
final class IntArray implements Iterable<Integer> {

	private int[] array;
	private int size;
	private int capacity;

	IntArray() {
		array = new int[0];
		size = 0;
		capacity = 0;
	}

	int get(int idx) {
		if (idx < 0 || idx >= size) {
			throw new ArrayIndexOutOfBoundsException();
		}

		return array[idx];
	}

	void set(int idx, int val) {
		if (idx < 0 || idx >= size) {
			throw new ArrayIndexOutOfBoundsException();
		}

		array[idx] = val;
	}

	void add(int val) {
		if (size == capacity) {
			final int newCapacity = (capacity == 0) ? 4 : 2 * capacity;
			array = Arrays.copyOf(array, newCapacity);
			capacity = newCapacity;
		}

		array[size++] = val;
	}

	void clear() {
		array = new int[0];
		size = 0;
		capacity = 0;
	}

	int size() {
		return size;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof IntArray)) {
			return false;
		}

		final IntArray b = (IntArray) obj;

		if (b.size != size) {
			return false;
		}

		for (int i = 0; i < size; i++) {
			if (b.array[i] != array[i]) {
				return false;
			}
		}

		return true;
	}

	@Override
	public Iterator<Integer> iterator() {
		return new IntArrayIterator(array, 0, size);
	}

	private static final class IntArrayIterator implements Iterator<Integer> {
		private final int[] array;
		private final int last;
		private int idx;

		IntArrayIterator(int[] array, int first, int last) {
			assert 0 <= first && first <= last && last <= array.length;

			this.array = array;
			this.last = last;
			idx = first;
		}

		@Override
		public boolean hasNext() {
			return idx < last;
		}

		@Override
		public Integer next() {
			if (idx == last) {
				throw new ArrayIndexOutOfBoundsException();
			}

			return array[idx++];
		}
	}
}
