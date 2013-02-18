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

public class CuckooHashSet<E> extends AbstractSet<E> {
	/**
	 * Default hash size.  Hash size is the power of two of this number.
	 */
	private static final int defaultSizeLog2 = 5;
	
	protected static class StashList<E> {
		E entry;
		StashList<E> next;
		
		public StashList(E entry, StashList<E> next) {
			this.entry = entry;
			this.next = next;
		}
		
		public E getEntry() {
			return entry;
		}
		public StashList<E> getNext() {
			return next;
		}
	}
	
	protected int log2buckets = 5;
	protected Object[] buckets;
	protected StashList<E> stashList;
	private int size;
	
	public CuckooHashSet(int size) {
		this.log2buckets = log2(2*size);
		this.buckets = new Object[1 << log2buckets];
	}
	public CuckooHashSet() {
		this.log2buckets = defaultSizeLog2;
		this.buckets = new Object[1 << defaultSizeLog2];
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
        hash += (hash << 12);
        hash ^= (hash >>> 22);
        hash += (hash << 4);
        hash ^= (hash >>> 9);
        hash += (hash << 10);
        hash ^= (hash >>> 2);
        hash += (hash << 7);
        hash ^= (hash >>> 12);
        return hash;
	}
	
	protected final int hash1(int hash) {
		return hash & (buckets.length-1);
	}
	
	protected final int hash2(int hash) {
		/* This computes (hash % (n^2)) % n-1, with n = buckets.length,
		 * where 0 is mapped to n-1.
		 * This may return 0 only if hash % (n^2) is 0; this is so unlikely
		 * that it won't degrade performance of cuckoo hashing.
		 */
		hash = ((hash >>> log2buckets) & (buckets.length - 1))
			 + (hash & (buckets.length - 1));
		hash = (hash + (hash >>> log2buckets)) & (buckets.length - 1);
		return hash;
	}
	
	private boolean containsStash(Object object) {
		StashList<E> stash = this.stashList;
		while (stash != null) {
			if (object.equals(stash.entry))
				return true;
			stash = stash.next;
		}
		return false;
	}
	
	public boolean contains(Object object) {
		int hash = hash(object);
		int hash1 = hash1(hash);
		if (object.equals(buckets[hash1]))
			return true;
		if (object.equals(buckets[hash2(hash) ^ hash1]))
			return true;
		return stashList != null && containsStash(object);
	}
	
	@SuppressWarnings("unchecked")
	private void resize() {
		Object[] oldbuckets = buckets;
		StashList<E> oldstash = stashList;
		stashList = null;
		log2buckets++;
		buckets = new Object[1 << log2buckets];
		for (int i = 0; i < oldbuckets.length; i++) {
			if (oldbuckets[i] != null) {
				add_internal(hash1(hash(oldbuckets[i])), (E) oldbuckets[i]);
			}
		}
		while (oldstash != null) {
			add_internal(hash1(hash(oldstash.entry)), oldstash.entry);
			oldstash = oldstash.next;
		}
	}
	
	@SuppressWarnings("unchecked")
	private void add_internal(int hash, E toAdd) {
		int maxIter = buckets.length>>2;
		while (true) {
			assert checkpos(hash);
			Object spill = buckets[hash];
			buckets[hash] = toAdd;
			assert checkpos(hash);
			if (spill == null)
				return;
			toAdd = (E) spill;
			hash ^= hash2(hash(toAdd));
			if (maxIter-- == 0) {
				if (3*size < buckets.length) {
					/* Use stash instead of resizing */
					stashList = new StashList<E>(toAdd, stashList);
					return;
				} else {
					resize();
					maxIter = buckets.length>>2;
					hash = hash1(hash(toAdd));
				}
			}
		}
	}
	
	private boolean checkpos(int i) {
		if (buckets[i] != null) {
			int hash = hash(buckets[i]);
			int hash1 = hash1(hash);
			int hash2 = hash1 ^ hash2(hash);
			assert(hash1 == i || hash2==i);
		}
		return true;
	}
	
	private boolean invariant() {
		assert(size >= 0);
		int cnt = 0;
		for (int i = 0; i < buckets.length; i++) {
			assert checkpos(i);
			if (buckets[i] != null)
				cnt++;
		}
		StashList<E> stash = stashList;
		while (stash != null) {
			cnt++;
			stash = stash.next;
		}
		assert(size == cnt);
		return true;
	}
	
	public boolean add(E toAdd) {
		int hash = hash(toAdd);
		int hash1 = hash1(hash);
		if (toAdd.equals(buckets[hash1]))
			return false;
		if (toAdd.equals(buckets[hash2(hash) ^ hash1]))
			return false;
		if (stashList != null && containsStash(toAdd))
			return false;
		if (buckets[hash1] == null)
			buckets[hash1] = toAdd;
		else
			add_internal(hash1, toAdd);
		size++;
		return true;
	}
	
	public boolean remove(Object toRemove) {
		int hash = hash(toRemove);
		int hash1 = hash1(hash);
		if (toRemove.equals(buckets[hash1])) {
			size--;
			assert(size >= 0);
			buckets[hash1] = null;
			return true;
		}
		hash1 ^= hash2(hash);
		if (toRemove.equals(buckets[hash1])) {
			size--;
			assert(size >= 0);
			buckets[hash1] = null;
			return true;
		}
		if (stashList == null)
			return false;
		StashList<E> pre = null;
		StashList<E> stash = this.stashList;
		while (stash != null) {
			if (toRemove.equals(stash.entry)) {
				size--;
				assert(size >= 0);
				if (pre != null)
					pre.next = stash.next;
				else
					this.stashList = stash.next;
				assert invariant();
				return true;
			}
			pre = stash;
			stash = stash.next;
		}
		return false;		
	}
	
	private final static int log2(int size) {
		int i,j;
		for (i = 4, j = 2; i < size; i+=i, j++)
			/*empty*/;
		return j;
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int lastPos = -1;
			int pos = 0;
			StashList<E> pre = null;
			StashList<E> current = null;
			public boolean hasNext() {
				while (pos < buckets.length && buckets[pos] == null)
					pos++;
				if (pos < buckets.length)
					return true;
				if (current != null)
					return current.next != null;
				return stashList != null;
			}
			@SuppressWarnings("unchecked")
			public E next() {
				while (pos < buckets.length && buckets[pos] == null)
					pos++;
				lastPos = pos;
				if (pos < buckets.length)
					return (E) buckets[pos++];
				if (current == null) {
					current = stashList;
				} else {
					pre = current;
					current = current.next;
				}
				return current.entry;
			}
			public void remove() {
				if (lastPos < buckets.length)
					buckets[lastPos] = null;
				else if (pre != null) {
					pre.next = current.next;
					current = pre;
				} else {
					stashList = current.next;
					current = null;
				}
				size--;
				assert(size >= 0);
			}
		};
	}

	@Override
	public int size() {
		return size;
	}
	
	public void clear() {
		size = 0;
		for (int i = 0; i < buckets.length; i++)
			buckets[i] = null;
		stashList = null;
	}
	
	@SuppressWarnings("unchecked")
	public E removeSome() {
		if (size == 0)
			return null;
		size--;
		assert(size >= 0);
		if (stashList != null) {
			E entry = stashList.entry;
			stashList = stashList.next;
			return entry;
		}
		for (int i = 0; ; i++) {
			if (buckets[i] != null) {
				E entry = (E) buckets[i];
				buckets[i] = null;
				return entry;
			}
		}
	}
}
