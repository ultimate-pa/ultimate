/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractSet;
import java.util.Iterator;
import java.util.NoSuchElementException;

public class CuckooHashSet<E> extends AbstractSet<E> {
	/**
	 * Default hash size.  Hash size is the power of two of this number.
	 */
	private static final int DEFAULT_SIZE_LOG_2 = 5;

	protected int mLog2buckets = 5;
	protected Object[] mBuckets;
	protected E mStash;
	private int mSize;

	public CuckooHashSet(int size) {
		this.mLog2buckets = log2(2 * size);
		this.mBuckets = new Object[1 << mLog2buckets];
	}
	public CuckooHashSet() {
		this.mLog2buckets = DEFAULT_SIZE_LOG_2;
		this.mBuckets = new Object[1 << DEFAULT_SIZE_LOG_2];
	}

	/**
	 * The hash function.  This must have good bit distributing properties.
	 * We use Jenkins hash function on object hashcode.
	 * @param o the object to hash
	 * @return the hash code.
	 */
	protected int hash(Object o) {
		return hashJenkins(o.hashCode());
	}

	protected static int hashJenkins(int hash) {
		hash += (hash << 12);// NOCHECKSTYLE
		hash ^= (hash >>> 22);// NOCHECKSTYLE
		hash += (hash << 4);// NOCHECKSTYLE
		hash ^= (hash >>> 9);// NOCHECKSTYLE
		hash += (hash << 10);// NOCHECKSTYLE
		hash ^= (hash >>> 2);// NOCHECKSTYLE
		hash += (hash << 7);// NOCHECKSTYLE
		hash ^= (hash >>> 12);// NOCHECKSTYLE
		return hash;
	}

	protected final int hash1(int hash) {
		return hash & (mBuckets.length - 1);
	}

	protected final int hash2(int hash) {
		/*
		 * scramble hash to make hash2 independent of hash1.
		 */
		hash = hashJenkins(hash);
		/*
		 * This computes (hash % (n^2)) % (n-1) + 1, with n = buckets.length, except when hash == n^2-1 mod n^2.
		 *
		 * This may return 0 only if hash == n^2-1 mod n^2; this is so unlikely that it won't degrade performance of
		 * cuckoo hashing.
		 */
		hash = ((hash >>> mLog2buckets) & (mBuckets.length - 1)) + (hash & (mBuckets.length - 1)) + 1;
		hash = (hash + (hash >>> mLog2buckets)) & (mBuckets.length - 1);
		return hash;
	}

	private boolean containsStash(Object object) {
		return object.equals(mStash);
	}

	@Override
	public boolean contains(Object object) {
		final int hash = hash(object);
		final int hash1 = hash1(hash);
		if (object.equals(mBuckets[hash1])) {
			return true;
		}
		if (object.equals(mBuckets[hash2(hash) ^ hash1])) {
			return true;
		}
		return mStash != null && containsStash(object);
	}

	@SuppressWarnings("unchecked")
	private void resize() {
		final Object[] oldbuckets = mBuckets;
		E oldstash = mStash;
		mStash = null;
		mLog2buckets++;
		mBuckets = new Object[1 << mLog2buckets];
		for (int i = 0; i < oldbuckets.length; i++) {
			if (oldbuckets[i] != null) {
				add_internal(hash1(hash(oldbuckets[i])), (E) oldbuckets[i]);
			}
		}
		add_internal(hash1(hash(oldstash)), oldstash);
	}

	@SuppressWarnings("unchecked")
	private void add_internal(int hash, E toAdd) {
		int maxIter = mBuckets.length >> 2;
		boolean checkedStash = false;
		while (true) {
			assert checkpos(hash);
			final Object spill = mBuckets[hash];
			mBuckets[hash] = toAdd;
			assert checkpos(hash);
			if (spill == null) {
				return;
			}
			toAdd = (E) spill;
			hash ^= hash2(hash(toAdd));
			if (maxIter-- == 0) {
				if (mStash == null) {
					/* Use stash instead of resizing */
					mStash = toAdd;
					return;
				}

				if (!checkedStash) {
					E oldstash = mStash;
					mStash = toAdd;
					toAdd = oldstash;
					checkedStash = true;
				} else {
					resize();
				}
				maxIter = mBuckets.length >> 2;
				hash = hash1(hash(toAdd));
			}
		}
	}

	private boolean checkpos(int i) {
		if (mBuckets[i] != null) {
			final int hash = hash(mBuckets[i]);
			final int hash1 = hash1(hash);
			final int hash2 = hash1 ^ hash2(hash);
			assert(hash1 == i || hash2 == i);
		}
		return true;
	}

	private boolean invariant() {
		assert(mSize >= 0);
		int cnt = 0;
		for (int i = 0; i < mBuckets.length; i++) {
			assert checkpos(i);
			if (mBuckets[i] != null) {
				cnt++;
			}
		}
		if (mStash != null) {
			cnt++;
		}
		assert(mSize == cnt);
		return true;
	}

	@Override
	public boolean add(E toAdd) {
		final int hash = hash(toAdd);
		final int hash1 = hash1(hash);
		if (toAdd.equals(mBuckets[hash1])) {
			return false;
		}
		if (toAdd.equals(mBuckets[hash2(hash) ^ hash1])) {
			return false;
		}
		if (mStash != null && containsStash(toAdd)) {
			return false;
		}
		if (mBuckets[hash1] == null) {
			mBuckets[hash1] = toAdd;
		} else {
			add_internal(hash1, toAdd);
		}
		mSize++;
		return true;
	}

	@Override
	public boolean remove(Object toRemove) {
		final int hash = hash(toRemove);
		int hash1 = hash1(hash);
		if (toRemove.equals(mBuckets[hash1])) {
			mSize--;
			assert(mSize >= 0);
			mBuckets[hash1] = null;
			return true;
		}
		hash1 ^= hash2(hash);
		if (toRemove.equals(mBuckets[hash1])) {
			mSize--;
			assert mSize >= 0;
			mBuckets[hash1] = null;
			return true;
		}
		if (mStash != null && toRemove.equals(mStash)) {
			mSize--;
			assert mSize >= 0;
			mStash = null;
			return true;
		}
		return false;
	}

	private final static int log2(int size) {
		int i,j;
		for (i = 4, j = 2; i < size; i += i, j++) {
			/*empty*/;
		}
		return j;
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int mLastPos = -1;
			int mPos = 0;
			@Override
			public boolean hasNext() {
				while (mPos < mBuckets.length && mBuckets[mPos] == null) {
					mPos++;
				}
				if (mPos == mBuckets.length && mStash == null) {
					mPos++;
				}
				return mPos <= mBuckets.length;
			}
			@Override
			@SuppressWarnings("unchecked")
			public E next() {
				while (mPos < mBuckets.length && mBuckets[mPos] == null) {
					mPos++;
				}
				mLastPos = mPos;
				if (mPos < mBuckets.length) {
					return (E) mBuckets[mPos++];
				} else if (mPos == mBuckets.length && mStash != null) {
					mPos++;
					return mStash;
				}
				throw new NoSuchElementException();
			}
			@Override
			public void remove() {
				if (mLastPos < mBuckets.length) {
					mBuckets[mLastPos] = null;
				} else {
					mStash = null;
				}
				mSize--;
				assert(mSize >= 0);
			}
		};
	}

	@Override
	public int size() {
		return mSize;
	}

	@Override
	public void clear() {
		mSize = 0;
		for (int i = 0; i < mBuckets.length; i++) {
			mBuckets[i] = null;
		}
		mStash = null;
	}

	@SuppressWarnings("unchecked")
	public E removeSome() {
		if (mSize == 0) {
			return null;
		}
		mSize--;
		assert(mSize >= 0);
		if (mStash != null) {
			final E entry = mStash;
			mStash = null;
			return entry;
		}
		for (int i = 0; /* empty */; i++) {
			if (mBuckets[i] != null) {
				final E entry = (E) mBuckets[i];
				mBuckets[i] = null;
				return entry;
			}
		}
	}
}
