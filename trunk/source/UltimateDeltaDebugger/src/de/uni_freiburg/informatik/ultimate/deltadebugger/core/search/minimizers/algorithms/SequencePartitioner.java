package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.ListIterator;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.SequencePartitioner.SubsequenceBounds;

/**
 * Partition of a sequence of a certain size into n (almost) equally sized
 * parts.
 * 
 * If the sequence cannot be divided into equal sized parts, distribute the
 * remainder evenly across the trailing subsequences, so the last r subsequences
 * have exactly one element more than than the first n-r subsequences.
 */
public class SequencePartitioner implements Iterable<SubsequenceBounds> {
	final int sequenceSize;
	final int numParts;

	/**
	 * @param sequenceSize
	 * @param numParts
	 * @throws IllegalArgumentException
	 */
	public SequencePartitioner(int sequenceSize, int numParts) {
		if (sequenceSize < 0) {
			throw new IllegalArgumentException("negative size");
		}

		if (numParts < 1) {
			throw new IllegalArgumentException("cannot partition into less than one part");
		}

		this.numParts = numParts;
		this.sequenceSize = sequenceSize;
	}

	public int getSequenceSize() {
		return sequenceSize;
	}

	public int getNumParts() {
		return numParts;
	}

	public SubsequenceBounds get(int index) {
		if (index < 0 || index >= numParts) {
			throw new IndexOutOfBoundsException();
		}

		int length = sequenceSize / numParts;
		int offset = index * length;

		int remainder = sequenceSize % numParts;
		int shift = index - (numParts - remainder);
		if (shift >= 0) {
			length += 1;
			offset += shift;
		}

		return new SubsequenceBounds(offset, offset + length);
	}

	@Override
	public ListIterator<SubsequenceBounds> iterator() {
		return listIterator(0);
	}

	public ListIterator<SubsequenceBounds> listIterator(int index) {
		return new SubsequenceIterator(index);
	}

	class SubsequenceIterator implements ListIterator<SubsequenceBounds> {
		int cursor;

		SubsequenceIterator(int index) {
			cursor = index;
		}

		@Override
		public boolean hasNext() {
			return cursor != sequenceSize;
		}

		@Override
		public boolean hasPrevious() {
			return cursor != 0;
		}

		@Override
		public SubsequenceBounds next() {
			int i = cursor;
			if (i >= numParts) {
				throw new NoSuchElementException();
			}
			cursor = i + 1;
			return get(i);
		}

		@Override
		public SubsequenceBounds previous() {
			int i = cursor - 1;
			if (cursor < 0) {
				throw new NoSuchElementException();
			}
			cursor = i;
			return get(i);
		}

		@Override
		public int nextIndex() {
			return cursor;
		}

		@Override
		public int previousIndex() {
			return cursor - 1;
		}

		@Override
		public void add(SubsequenceBounds e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void set(SubsequenceBounds e) {
			throw new UnsupportedOperationException();
		}
	}

	public static final class SubsequenceBounds {
		private final int begin;
		private final int end;

		public SubsequenceBounds(int begin, int end) {
			this.begin = begin;
			this.end = end;
		}

		public int getBegin() {
			return begin;
		}

		public int getEnd() {
			return end;
		}

		public int getSize() {
			return end - begin;
		}

		@Override
		public String toString() {
			return "[" + begin + ", " + end + ")";
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + begin;
			result = prime * result + end;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			SubsequenceBounds other = (SubsequenceBounds) obj;
			if (begin != other.begin)
				return false;
			if (end != other.end)
				return false;
			return true;
		}
	}
}