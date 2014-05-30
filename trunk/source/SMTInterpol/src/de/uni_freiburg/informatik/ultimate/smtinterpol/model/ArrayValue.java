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

import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ArrayValue {

	private static class Entry {
		private final int mKey;
		private int mValue;
		private Entry mNext;
		private Entry mListNext, mListPrev; // NOPMD
		Entry() {
			mKey = -2;
			mValue = -2;
			mNext = null;
			mListNext = mListPrev = this;
		}
		public Entry(int key, int value, Entry next, Entry sentinel) {
			mKey = key;
			mValue = value;
			mNext = next;
			mListNext = sentinel;
			mListPrev = sentinel.mListPrev;
			sentinel.mListPrev.mListNext = this;
			sentinel.mListPrev = this;
		}
		public void unlink() {
			mListNext.mListPrev = mListPrev;
			mListPrev.mListNext = mListNext;
		}
		public int getKey() {
			return mKey;
		}
		public int getValue() {
			return mValue;
		}
		public int setValue(int value) {
			int res = mValue;
			mValue = value;
			return res;
		}
		public int hashCode() {
			return mKey + 3643 * mValue;
		}
		public String toString() {
			return "[" + mKey + "," + mValue + "]";
		}
	}
	
	private static class IntIntMap {	
		Entry[] mTable;
		int mSize;
		int mThreshold;
		final Entry mList;
		private final static float LOAD_FACTOR = 0.75f;
		public IntIntMap() {
			this(8);
		}
		public IntIntMap(int capacity) {
			mTable = new Entry[capacity];
			mSize = 0;
			mThreshold = (int) (capacity * LOAD_FACTOR);
			mList = new Entry();
		}
		public IntIntMap(IntIntMap other) {
			mTable = new Entry[other.mTable.length];
			mSize = 0;
			mThreshold = other.mThreshold;
			mList = new Entry();
			for (Entry e : other.forwardInsertionOrder())
				add(e.getKey(), e.getValue());
		}
		private int idx2bucket(int idx) {
			return idx & (mTable.length - 1);
		}
		
		private void grow() {
			Entry[] old = mTable;
			mTable = new Entry[mTable.length << 1];
			mThreshold = (int) (mTable.length * LOAD_FACTOR);
			for (Entry e : old) {
				for (Entry bucket = e; bucket != null; ) {
					int idx = idx2bucket(bucket.mKey);
					Entry reinsert = bucket;
					bucket = bucket.mNext;
					reinsert.mNext = mTable[idx];
					mTable[idx] = reinsert;
				}
			}
		}
		
		public int add(int key, int value) {
			if (mSize >= mThreshold)
				grow();
			int hash = idx2bucket(key);
			Entry e = findEntry(hash, key);
			if (e == null) {
				++mSize;
				e = new Entry(key, value, mTable[hash], mList);
				mTable[hash] = e;
				return value;
			}
			return e.setValue(value);
		}
		
		public int remove(int key) {
			int hash = idx2bucket(key);
			Entry prev = null;
			for (Entry bucket = mTable[hash]; bucket != null;
					bucket = bucket.mNext) {
				if (bucket.getKey() == key) {
					bucket.unlink();
					if (prev == null)
						mTable[hash] = bucket.mNext;
					else
						prev.mNext = bucket.mNext;
					--mSize;
					return bucket.getValue();
				}
				prev = bucket;
			}
			return 0;
		}
		
		public int get(int key, boolean partial) {
			int hash = idx2bucket(key);
			Entry e = findEntry(hash, key);
			if (e == null)
				return partial ? -1 : 0;
			return e.getValue();
		}

		private Entry findEntry(int hash, int key) {
			for (Entry bucket = mTable[hash]; bucket != null;
					bucket = bucket.mNext)
				if (bucket.getKey() == key)
					return bucket;
			return null;
		}
		
		public boolean containsKey(int key) {
			int hash = idx2bucket(key);
			return findEntry(hash, key) != null;
		}
		
		public int getSize() {
			return mSize;
		}
		
		public int hashCode() {
			int hash = 0;
			for (Entry e : forwardInsertionOrder())
				hash += e.hashCode();
			return hash;
		}
		
		public boolean equals(Object other) {
			if (!(other instanceof IntIntMap))
				return false;
			IntIntMap o = (IntIntMap) other;
			if (o.getSize() != mSize)
				return false;
			for (Entry e : o.forwardInsertionOrder()) {
				int hash = idx2bucket(e.getKey());
				Entry my = findEntry(hash, e.getKey());
				if (my == null || my.getValue() != e.getValue())
					return false;
			}
			return true;
		}
		
		public Iterable<Entry> forwardInsertionOrder() {
			return new Iterable<ArrayValue.Entry>() {
				
				@Override
				public Iterator<Entry> iterator() {
					return new Iterator<ArrayValue.Entry>() {

						private Entry mCur = mList.mListNext;
						
						@Override
						public boolean hasNext() {
							return mCur != mList;
						}

						@Override
						public Entry next() {
							Entry cur = mCur;
							mCur = mCur.mListNext;
							return cur;
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
				}
			};
			
		}

		public Iterable<Entry> backwardInsertionOrder() {
			return new Iterable<ArrayValue.Entry>() {
				
				@Override
				public Iterator<Entry> iterator() {
					return new Iterator<ArrayValue.Entry>() {

						private Entry mCur = mList.mListPrev;
						
						@Override
						public boolean hasNext() {
							return mCur != mList;
						}

						@Override
						public Entry next() {
							Entry cur = mCur;
							mCur = mCur.mListPrev;
							return cur;
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
				}
			};
			
		}
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append('{');
			for (Entry e : forwardInsertionOrder())
				sb.append(e);
			sb.append('}');
			return sb.toString();
		}
	}
	
	public final static ArrayValue DEFAULT_ARRAY = new ArrayValue(null);
	
	private final IntIntMap mValues;
	private IntIntMap mDiffMap;
	
	public ArrayValue() {
		this(new IntIntMap());
	}
	
	private ArrayValue(IntIntMap map) {
		mValues = map;
		mDiffMap = null;
	}
	
	public int store(int idx, int val) {
		if (val == 0)
			return mValues.remove(idx);
		return mValues.add(idx, val);
	}
	
	public int select(int idx, boolean partial) {
		return mValues == null ? 0 : mValues.get(idx, partial);
	}
	
	public int hashCode() {
		return mValues == null ? 0 : mValues.hashCode();
	}
	
	public boolean equals(Object other) {
		if (!(other instanceof ArrayValue))
			return false;
		if (this == DEFAULT_ARRAY)
			return other == DEFAULT_ARRAY;
		return mValues.equals(((ArrayValue) other).mValues);
	}
	
	ArrayValue copy() {
		IntIntMap copy = mValues == null
				? new IntIntMap() : new IntIntMap(mValues);
		return new ArrayValue(copy);
	}

	public Term toSMTLIB(Sort s, Theory t,
			SortInterpretation index, SortInterpretation value) {
		Term res = t.term(t.getFunctionWithResult("@0", null, s));
		if (mValues.getSize() != 0) {
			Sort indexSort = s.getArguments()[0];
			Sort valueSort = s.getArguments()[1];
			FunctionSymbol store = t.getFunction(
					"store", s, indexSort, valueSort);
			for (Entry e : mValues.backwardInsertionOrder())
				res = t.term(store, res, index.get(e.getKey(), indexSort, t),
						value.get(e.getValue(), valueSort, t));
		}
		return res;
	}

	public boolean containsMapping(int val) {
		return mValues == null ? false : mValues.containsKey(val);
	}
	
	public void addDiff(int snd, int val) {
		if (mDiffMap == null)
			mDiffMap = new IntIntMap();
		mDiffMap.add(snd, val);
	}
	
	public int computeDiff(int idx, ArrayValue other) {
		if (mValues == null)
			return other == this ? 0 : other.computeDiff(0, this);
		// diffs
		if (mDiffMap != null && mDiffMap.containsKey(idx))
			return mDiffMap.get(idx, false);
		// no diff matches
		for (Entry e : mValues.forwardInsertionOrder()) {
			if (other.select(e.getKey(), false) != e.getValue())
				return e.getKey();
		}
		assert this == other;
		return 0;
	}
	
	public String toString() {
		return mValues == null ? "@0" : mValues.toString();
	}
}
