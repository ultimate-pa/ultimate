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
			final int res = mValue;
			mValue = value;
			return res;
		}

		@Override
		public int hashCode() {
			return mKey + 3643 * mValue;
		}

		@Override
		public String toString() {
			return "[" + mKey + "->" + mValue + "]";
		}
	}

	private static class IntIntMap {
		Entry[] mTable;
		int mDefaultValue;
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
			mDefaultValue = 0;
			mThreshold = (int) (capacity * LOAD_FACTOR);
			mList = new Entry();
		}

		public IntIntMap(IntIntMap other) {
			mTable = new Entry[other.mTable.length];
			mSize = 0;
			mDefaultValue = other.mDefaultValue;
			mThreshold = other.mThreshold;
			mList = new Entry();
			for (final Entry e : other.forwardInsertionOrder()) {
				add(e.getKey(), e.getValue());
			}
		}

		private int idx2bucket(int idx) {
			return idx & (mTable.length - 1);
		}

		private void grow() {
			final Entry[] old = mTable;
			mTable = new Entry[mTable.length << 1];
			mThreshold = (int) (mTable.length * LOAD_FACTOR);
			for (final Entry e : old) {
				for (Entry bucket = e; bucket != null;) {
					final int idx = idx2bucket(bucket.mKey);
					final Entry reinsert = bucket;
					bucket = bucket.mNext;
					reinsert.mNext = mTable[idx];
					mTable[idx] = reinsert;
				}
			}
		}

		public int add(int key, int value) {
			if (value == mDefaultValue) {
				return remove(key);
			}
			if (mSize >= mThreshold) {
				grow();
			}
			final int hash = idx2bucket(key);
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
			final int hash = idx2bucket(key);
			Entry prev = null;
			for (Entry bucket = mTable[hash]; bucket != null; bucket = bucket.mNext) {
				if (bucket.getKey() == key) {
					bucket.unlink();
					if (prev == null) {
						mTable[hash] = bucket.mNext;
					} else {
						prev.mNext = bucket.mNext;
					}
					--mSize;
					return bucket.getValue();
				}
				prev = bucket;
			}
			return 0;
		}

		public int get(int key) {
			final int hash = idx2bucket(key);
			final Entry e = findEntry(hash, key);
			if (e == null) {
				return mDefaultValue;
			}
			return e.getValue();
		}

		private Entry findEntry(int hash, int key) {
			for (Entry bucket = mTable[hash]; bucket != null; bucket = bucket.mNext) {
				if (bucket.getKey() == key) {
					return bucket;
				}
			}
			return null;
		}

		public boolean containsKey(int key) {
			final int hash = idx2bucket(key);
			return findEntry(hash, key) != null;
		}

		public int getSize() {
			return mSize;
		}

		@Override
		public int hashCode() {
			int hash = 0; // mDefaultValue;
			for (final Entry e : forwardInsertionOrder()) {
				hash += e.hashCode();
			}
			return hash;
		}

		@Override
		public boolean equals(Object other) {
			if (!(other instanceof IntIntMap)) {
				return false;
			}
			final IntIntMap o = (IntIntMap) other;
			if (o.getSize() != mSize) {
				return false;
			}
			if (o.mDefaultValue != mDefaultValue) {
				return false;
			}
			for (final Entry e : o.forwardInsertionOrder()) {
				final int hash = idx2bucket(e.getKey());
				final Entry my = findEntry(hash, e.getKey());
				if (my == null || my.getValue() != e.getValue()) {
					return false;
				}
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
							final Entry cur = mCur;
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
							final Entry cur = mCur;
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

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append('{');
			for (final Entry e : forwardInsertionOrder()) {
				sb.append(e);
			}
			sb.append("[default->").append(mDefaultValue).append(']');
			sb.append('}');
			return sb.toString();
		}
	}

	public final static ArrayValue DEFAULT_ARRAY = new ArrayValue(new IntIntMap(1));

	private final IntIntMap mValues;
	private IntIntMap mDiffMap;

	public ArrayValue() {
		this(new IntIntMap());
	}

	private ArrayValue(IntIntMap map) {
		mValues = map;
		mDiffMap = null;
	}

	public void setDefaultValue(int val) {
		mValues.mDefaultValue = val;
	}

	public int store(int idx, int val) {
		return mValues.add(idx, val);
	}

	public int select(int idx) {
		return mValues.get(idx);
	}

	@Override
	public int hashCode() {
		return mValues.hashCode();
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof ArrayValue)) {
			return false;
		}
		if (this == other) {
			return true;
		}
		return mValues.equals(((ArrayValue) other).mValues);
	}

	ArrayValue copy() {
		final IntIntMap copy = mValues == null ? new IntIntMap() : new IntIntMap(mValues);
		return new ArrayValue(copy);
	}

	public Term toSMTLIB(Sort s, Theory t, SortInterpretation index, SortInterpretation value) {
		final Sort indexSort = s.getArguments()[0];
		final Sort valueSort = s.getArguments()[1];
		Term res = t.term(t.getFunctionWithResult("const", null, s, valueSort),
				value.get(mValues.mDefaultValue, valueSort, t));
		if (mValues.getSize() != 0) {
			final FunctionSymbol store = t.getFunction("store", s, indexSort, valueSort);
			for (final Entry e : mValues.backwardInsertionOrder()) {
				res = t.term(store, res, index.get(e.getKey(), indexSort, t), value.get(e.getValue(), valueSort, t));
			}
		}
		return res;
	}

	public boolean containsMapping(int val) {
		return mValues == null ? false : mValues.containsKey(val);
	}

	public void addDiff(int snd, int val) {
		if (mDiffMap == null) {
			mDiffMap = new IntIntMap();
		}
		mDiffMap.add(snd, val);
	}

	public int computeDiff(int otherIdx, ArrayValue other, ArraySortInterpretation sort) {
		// first check diff map
		if (mDiffMap != null && mDiffMap.containsKey(otherIdx)) {
			return mDiffMap.get(otherIdx);
		}
		if (this == other) {
			return 0;
		}
		// no diff matches; search first explicit difference
		for (final Entry e : mValues.forwardInsertionOrder()) {
			if (other.select(e.getKey()) != e.getValue()) {
				return e.getKey();
			}
		}
		// search all indices
		for (int index = 0; index < sort.getIndexInterpretation().size(); index++) {
			if (select(index) != other.select(index)) {
				return index;
			}
		}
		// they must differ on default value, so just return a fresh value.
		return sort.getIndexInterpretation().extendFresh();
	}

	@Override
	public String toString() {
		return mValues.toString();
	}
}
