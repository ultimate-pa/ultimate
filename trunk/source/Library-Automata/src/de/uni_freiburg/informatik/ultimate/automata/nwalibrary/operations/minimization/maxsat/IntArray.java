package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.Arrays;
import java.util.Iterator;

public class IntArray implements Iterable<Integer> {
	private int[] array;
	private int size;
	private int capacity;

	public IntArray() {
		array = new int[0];
		size = 0;
		capacity = 0;
	}

	public int get(int idx) {
		if (idx < 0 || idx >= size)
			throw new ArrayIndexOutOfBoundsException();
		return array[idx];
	}

	public void set(int idx, int val) {
		if (idx < 0 || idx >= size)
			throw new ArrayIndexOutOfBoundsException();
		array[idx] = val;
	}

	public void add(int val) {
		if (size == capacity) {
			int newCapacity = (capacity == 0) ? 4 : 2 * capacity;
			array = Arrays.copyOf(array, newCapacity);
			capacity = newCapacity;
		}
		array[size++] = val;
	}

	public void clear() {
		array = new int[0];
		size = 0;
		capacity = 0;
	}

	public int size() {
		return size;
	}

	public boolean equals(IntArray b) {
		if (b == null)
			return false;
		if (b.size != size)
			return false;
		for (int i = 0; i < size; i++)
			if (b.array[i] != array[i])
				return false;
		return true;
	}

	@Override
	public Iterator<Integer> iterator() {
		return new IntArrayIterator(array, 0, size);
	}

	public static class IntArrayIterator implements Iterator<Integer> {
		private final int[] array;
		private final int last;
		private int idx;

		public IntArrayIterator(int[] array, int first, int last) {
			assert 0 <= first && first <= last && last <= array.length;

			this.array = array;
			this.last = last;
			this.idx = first;
		}

		@Override
		public boolean hasNext() {
			return idx < last;
		}

		@Override
		public Integer next() {
			if (idx == last)
				throw new ArrayIndexOutOfBoundsException();

			return array[idx++];
		}
	}
}