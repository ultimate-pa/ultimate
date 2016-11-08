package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.ListIterator;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.SequencePartitioner.SubsequenceBounds;

/**
 * Partition of a sequence of a certain size into n (almost) equally sized parts.
 *
 * If the sequence cannot be divided into equal sized parts, distribute the remainder evenly across the trailing
 * subsequences, so the last r subsequences have exactly one element more than than the first n-r subsequences.
 */
public class SequencePartitioner implements Iterable<SubsequenceBounds> {
	public static final class SubsequenceBounds {
		private final int mBegin;
		private final int mEnd;

		public SubsequenceBounds(final int begin, final int end) {
			mBegin = begin;
			mEnd = end;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SubsequenceBounds other = (SubsequenceBounds) obj;
			if (mBegin != other.mBegin) {
				return false;
			}
			if (mEnd != other.mEnd) {
				return false;
			}
			return true;
		}

		public int getBegin() {
			return mBegin;
		}

		public int getEnd() {
			return mEnd;
		}

		public int getSize() {
			return mEnd - mBegin;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + mBegin;
			result = prime * result + mEnd;
			return result;
		}

		@Override
		public String toString() {
			return "[" + mBegin + ", " + mEnd + ")";
		}
	}

	class SubsequenceIterator implements ListIterator<SubsequenceBounds> {
		private int mCursor;

		SubsequenceIterator(final int index) {
			mCursor = index;
		}

		@Override
		public void add(final SubsequenceBounds e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean hasNext() {
			return mCursor != mSequenceSize;
		}

		@Override
		public boolean hasPrevious() {
			return mCursor != 0;
		}

		@Override
		public SubsequenceBounds next() {
			final int i = mCursor;
			if (i >= mNumParts) {
				throw new NoSuchElementException();
			}
			mCursor = i + 1;
			return get(i);
		}

		@Override
		public int nextIndex() {
			return mCursor;
		}

		@Override
		public SubsequenceBounds previous() {
			if (mCursor < 0) {
				throw new NoSuchElementException();
			}
			final int i = mCursor - 1;
			mCursor = i;
			return get(i);
		}

		@Override
		public int previousIndex() {
			return mCursor - 1;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void set(final SubsequenceBounds e) {
			throw new UnsupportedOperationException();
		}
	}

	private final int mSequenceSize;

	private final int mNumParts;

	/**
	 * @param sequenceSize
	 * @param numParts
	 * @throws IllegalArgumentException
	 */
	public SequencePartitioner(final int sequenceSize, final int numParts) {
		if (sequenceSize < 0) {
			throw new IllegalArgumentException("negative size");
		}

		if (numParts < 1) {
			throw new IllegalArgumentException("cannot partition into less than one part");
		}

		this.mNumParts = numParts;
		this.mSequenceSize = sequenceSize;
	}

	public SubsequenceBounds get(final int index) {
		if (index < 0 || index >= mNumParts) {
			throw new IndexOutOfBoundsException();
		}

		int length = mSequenceSize / mNumParts;
		int offset = index * length;

		final int remainder = mSequenceSize % mNumParts;
		final int shift = index - (mNumParts - remainder);
		if (shift >= 0) {
			length += 1;
			offset += shift;
		}

		return new SubsequenceBounds(offset, offset + length);
	}

	public int getNumParts() {
		return mNumParts;
	}

	public int getSequenceSize() {
		return mSequenceSize;
	}

	@Override
	public ListIterator<SubsequenceBounds> iterator() {
		return listIterator(0);
	}

	public ListIterator<SubsequenceBounds> listIterator(final int index) {
		return new SubsequenceIterator(index);
	}
}
