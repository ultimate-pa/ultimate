/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.NoSuchElementException;

/**
 * A bidirectional map from int to E.
 * @author Juergen Christ
 */
public class BidiMap<E> {

	private static class Entry<E> {
		final int mIdx;
		final E mVal;
		
		final int mHash;
		
		Entry<E> mNextIdx;
		Entry<E> mNextVal;
		
		public Entry(int idx, E val, int hash) {
			mIdx = idx;
			mVal = val;
			mHash = hash;
			mNextIdx = null;
			mNextVal = null;
		}
		
		public int getIdx() {
			return mIdx;
		}
		
		public E getValue() {
			return mVal;
		}
		
		@Override
		public String toString() {
			return "[" + mIdx + "," + mVal + "]";
		}
	}
	
	private static int roundUpToPowerOf2(int number) {
		// assert number >= 0 : "number must be non-negative";
		int rounded = number >= MAXIMUM_CAPACITY
				? MAXIMUM_CAPACITY
					: (rounded = Integer.highestOneBit(number)) != 0 //NOPMD
					? (Integer.bitCount(number) > 1) ? rounded << 1 : rounded
						: 1;
		return rounded;
	}
	
	private Entry<E>[] mIntTable;
	private Entry<E>[] mValTable;
	
	private int mSize;
	private int mThreshold;
	private float mLoadFactor;
	
	private Entry<E> mLastEntry;
	
	public final static float DEFAULT_LOAD_FACTOR = 0.75f;
	public final static int DEFAULT_SIZE = 8;
	
	public final static int MAXIMUM_CAPACITY = 1 << 30; // NOCHECKSTYLE
	
	public BidiMap() {
		this(DEFAULT_SIZE, DEFAULT_LOAD_FACTOR);
	}
	
	public BidiMap(int size) {
		this(size, DEFAULT_LOAD_FACTOR);
	}
	
	public BidiMap(int size, float loadFactor) {
		mSize = 0;
		mLoadFactor = loadFactor;
		init(roundUpToPowerOf2(size));
	}
	
	@SuppressWarnings("unchecked")
	private void init(int size) {
		mIntTable = new Entry[size];
		mValTable = new Entry[size];
		mThreshold = (int) (size * mLoadFactor);
	}
	
	private final int hash(E val) {
		int h = 0;
		h ^= val.hashCode();

		// This function ensures that hashCodes that differ only by
		// constant multiples at each bit position have a bounded
		// number of collisions (approximately 8 at default load factor).
		h ^= (h >>> 20) ^ (h >>> 12); // NOCHECKSTYLE
		return h ^ (h >>> 7) ^ (h >>> 4); // NOCHECKSTYLE
	}

	private final int intBucketIdx(int idx) {
		return idx & (mIntTable.length - 1);
	}
	
	private final int valBucketIdx(int hash) {
		return hash & (mValTable.length - 1);
	}
	
	/**
	 * Add a new mapping.  Note that this map does not support null keys.  If
	 * either the key or the value is already known, the map is not changed and
	 * <code>false</code> is returned.  Otherwise, the new mapping is created.
	 * @param idx The index.
	 * @param val The value.
	 * @return Did we actually change the mapping?
	 * @throws NullPointerException If <code>val</code> is <code>null</code>.
	 */
	public boolean add(int idx, E val) {
		final int hash = hash(val);
		final Entry<E> newEntry = new Entry<E>(idx, val, hash);
		if (canInsert(newEntry)) {
			mLastEntry = null;
			if (++mSize >= mThreshold) {
				grow();
			}
			insertInt(newEntry);
			insertVal(newEntry);
			return true;
		}
		mLastEntry = null;
		return false;
	}
	
	@SuppressWarnings("unchecked")
	private void grow() {
		int newCapacity = mIntTable.length << 1;
		if (newCapacity > MAXIMUM_CAPACITY) {
			newCapacity = MAXIMUM_CAPACITY;
		}
		mThreshold = (int) (newCapacity * mLoadFactor);
		// Rehashing
		final Entry<E>[] oldIntTable = mIntTable;
		final Entry<E>[] oldValTable = mValTable;
		mIntTable = new Entry[newCapacity];
		mValTable = new Entry[newCapacity];
		for (int i = 0; i < oldIntTable.length; ++i) {
			for (Entry<E> bucket = oldIntTable[i]; bucket != null; ) {
				final Entry<E> reinsert = bucket;
				bucket = bucket.mNextIdx;
				insertInt(reinsert);
			}
		}
		for (int i = 0; i < oldValTable.length; ++i) {
			for (Entry<E> bucket = oldValTable[i]; bucket != null; ) {
				final Entry<E> reinsert = bucket;
				bucket = bucket.mNextVal;
				insertVal(reinsert);
			}
		}
	}
	
	private Entry<E> getEntryByIdx(int idx) {
		final int b = intBucketIdx(idx);
		for (Entry<E> bucket = mIntTable[b]; bucket != null;
				bucket = bucket.mNextIdx) {
			if (bucket.mIdx == idx) {
				return mLastEntry = bucket;
			}
		}
		return null;
	}
	
	private Entry<E> getEntryByVal(E val) {
		final int hash = hash(val);
		final int b = valBucketIdx(hash);
		for (Entry<E> bucket = mValTable[b]; bucket != null;
				bucket = bucket.mNextVal) {
			// Compare on full hash to reduce equals comparisons
			if (bucket.mHash == hash && bucket.mVal.equals(val)) {
				return mLastEntry = bucket;
			}
		}
		return null;
	}
	
	private boolean canInsert(Entry<E> newEntry) {
		return getEntryByIdx(newEntry.mIdx) == null
				&& getEntryByVal(newEntry.mVal) == null;
	}
	
	private void insertInt(Entry<E> newEntry) {
		final int idx = intBucketIdx(newEntry.mIdx);
		newEntry.mNextIdx = mIntTable[idx];
		mIntTable[idx] = newEntry;
	}
	
	private void insertVal(Entry<E> newEntry) {
		final int idx = valBucketIdx(newEntry.mHash);
		newEntry.mNextVal = mValTable[idx];
		mValTable[idx] = newEntry;
	}
	
	public E get(int idx) {
		if (mLastEntry != null && mLastEntry.mIdx == idx) {
			return mLastEntry.getValue();
		}
		final Entry<E> bucket = getEntryByIdx(idx);
		return bucket == null ? null : bucket.getValue();
	}
	
	public int get(E val) {
		if (mLastEntry != null) {
			final int hash = hash(val);
			if (mLastEntry.mHash == hash && mLastEntry.mVal.equals(val)) {
				return mLastEntry.getIdx();
			}
		}
		final Entry<E> bucket = getEntryByVal(val);
		if (bucket == null) {
			throw new NoSuchElementException();
		}
		return bucket.getIdx();
	}
	
	public boolean containsIdx(int idx) {
		return getEntryByIdx(idx) != null;
	}
	
	public boolean containsVal(E val) {
		return getEntryByVal(val) != null;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('{');
		for (final Entry<E> outer : mIntTable) {
			for (Entry<E> bucket = outer; bucket != null;
					bucket = bucket.mNextIdx) {
				sb.append(bucket);
			}
		}
		sb.append('}');
		return sb.toString();
	}

	public int size() {
		return mSize;
	}
	
}
