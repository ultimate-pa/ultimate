/*
 * Copyright (C) 2014-2017 Daniel Tischner <zabuza.dev@gmail.com>
 * Copyright (C) 2009-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;

/**
 * Extends {@link HashSet} by a cache for the current hash code value returned
 * by {@link #hashCode()}. This means that if there is a valid cache, calls to
 * {@link #hashCode()} are computed in <tt>O(1)</tt> instead of
 * <tt>O(n)</tt>.<br/>
 * This makes the set considerable for usage as <tt>key</tt> in {@link Map Maps}
 * or similar data structures. <br/>
 * <br/>
 * The cache is automatically cleared every time the set is modified, for
 * example by {@link #add(Object)} or {@link #remove(Object)}. The cache can be
 * cleared manually by invoking {@link #clearHashCache()}.<br/>
 * <br/>
 * Note that direct modifications of this sets elements which change their hash
 * code value must not be done. Otherwise the cashed hash becomes invalid but
 * not automatically cleared. Also, as in a regular {@link HashSet}, the set
 * will not be able to find its elements anymore. If such a modification is
 * necessary consider re-adding the element.<br/>
 * <br/>
 * Note that this implementation is not synchronized.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <E>
 *            The type of elements maintained by this set
 */
public final class CachedHashSet<E> extends HashSet<E> {
	/**
	 * Serial version UID.
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * The hash code value currently cashed. The value is considered to be valid if
	 * {@link #mHasCachedHash} is set to <tt>true</tt>.
	 */
	private int mCachedHash = 0;
	/**
	 * Whether the set currently has a hash code value cached. Setting this flag to
	 * <tt>false</tt> implicitly clears the cache.
	 */
	private boolean mHasCachedHash = false;

	/**
	 * Constructs a new, empty set.
	 * 
	 * @see HashSet#HashSet()
	 */
	public CachedHashSet() {
		super();
	}

	/**
	 * Constructs a new set containing the elements in the specified collection.
	 * 
	 * @param collection
	 *            The collection whose elements are to be placed into this set
	 * 
	 * @see HashSet#HashSet(int)
	 */
	public CachedHashSet(final Collection<? extends E> collection) {
		super(collection);
	}

	/**
	 * Constructs a new, empty set with the specified initial capacity.
	 * 
	 * @param initialCapacity
	 *            The initial capacity of the hash table
	 * 
	 * @see HashSet#HashSet()
	 */
	public CachedHashSet(final int initialCapacity) {
		super(initialCapacity);
	}

	/**
	 * Constructs a new, empty set with the specified initial capacity and load
	 * factor.
	 * 
	 * @param initialCapacity
	 *            The initial capacity of the hash set
	 * @param loadFactor
	 *            The load factor of the hash set
	 * 
	 * @see HashSet#HashSet(int, float)
	 */
	public CachedHashSet(final int initialCapacity, final float loadFactor) {
		super(initialCapacity, loadFactor);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.HashSet#add(java.lang.Object)
	 */
	@Override
	public boolean add(final E element) {
		final boolean wasModified = super.add(element);
		if (wasModified) {
			clearHashCache();
		}
		return wasModified;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.HashSet#clear()
	 */
	@Override
	public void clear() {
		super.clear();
		clearHashCache();
	}

	/**
	 * Clears the cache for the hash code. Causing the hash code value to be
	 * recomputed at the next call of {@link #hashCode()}.
	 */
	public void clearHashCache() {
		this.mHasCachedHash = false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.HashSet#clone()
	 */
	@Override
	public Object clone() {
		@SuppressWarnings("unchecked")
		final CachedHashSet<E> clonedSet = (CachedHashSet<E>) super.clone();
		clonedSet.clearHashCache();
		return clonedSet;
	}

	/**
	 * Computes and returns the hash code value for this set as defined in
	 * {@link HashSet#hashCode()}.<br/>
	 * <br/>
	 * Additionally caches the value to provide a fast <tt>O(1)</tt> computation if
	 * there is a valid cache.
	 * 
	 * @see java.util.AbstractSet#hashCode()
	 */
	@Override
	public int hashCode() {
		// Update cache if there is no value
		if (!this.mHasCachedHash) {
			this.mCachedHash = super.hashCode();
			this.mHasCachedHash = true;
		}

		// Return value from cache
		return this.mCachedHash;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.HashSet#remove(java.lang.Object)
	 */
	@Override
	public boolean remove(final Object object) {
		final boolean wasModified = super.remove(object);
		if (wasModified) {
			clearHashCache();
		}
		return wasModified;
	}
}
