/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.ListIterator;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.SequencePartitioner.SubsequenceBounds;

/**
 * Partition of a sequence of a certain size into n (almost) equally sized parts.
 * If the sequence cannot be divided into equal sized parts, distribute the remainder evenly across the trailing
 * subsequences, so the last r subsequences have exactly one element more than than the first n-r subsequences.
 */
public class SequencePartitioner implements Iterable<SubsequenceBounds> {
	private final int mSequenceSize;
	private final int mNumParts;
	
	/**
	 * @param sequenceSize
	 *            Sequence size.
	 * @param numParts
	 *            number of parts
	 */
	public SequencePartitioner(final int sequenceSize, final int numParts) {
		if (sequenceSize < 0) {
			throw new IllegalArgumentException("negative size");
		}
		
		if (numParts < 1) {
			throw new IllegalArgumentException("cannot partition into less than one part");
		}
		
		mNumParts = numParts;
		mSequenceSize = sequenceSize;
	}
	
	/**
	 * @param index
	 *            Index.
	 * @return subsequence bounds
	 */
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
	
	/**
	 * @param index
	 *            Index.
	 * @return list iterator over subsequence bounds
	 */
	public ListIterator<SubsequenceBounds> listIterator(final int index) {
		return new SubsequenceIterator(index);
	}
	
	/**
	 * Sequence bounds.
	 */
	public static final class SubsequenceBounds {
		private final int mBegin;
		private final int mEnd;
		
		/**
		 * @param begin
		 *            Start index.
		 * @param end
		 *            end index
		 */
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
	
	/**
	 * Sequence iterator.
	 */
	class SubsequenceIterator implements ListIterator<SubsequenceBounds> {
		private int mCursor;
		
		SubsequenceIterator(final int index) {
			mCursor = index;
		}
		
		@Override
		public void add(final SubsequenceBounds bounds) {
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
		public void set(final SubsequenceBounds bounds) {
			throw new UnsupportedOperationException();
		}
	}
}
