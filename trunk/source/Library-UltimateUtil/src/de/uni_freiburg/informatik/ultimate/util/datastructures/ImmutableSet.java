/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Represents an immutable set, i.e., a set that cannot be modified. Immutable sets are suitable as elements of sets of
 * sets, or keys in hash maps. Immutability allows to perform calls to {@link #hashCode()} in O(1) time.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <E>
 *            The type of elements in the set
 */
public final class ImmutableSet<E> implements Set<E> {
	private static final String ERROR_MSG = "Set is immutable";

	private final Set<E> mUnderlying;
	private final int mHash;

	/**
	 * Creates a new immutable set, with the given underlying set of elements. The caller must guarantee to prevent any
	 * modification of the underlying set.
	 *
	 * @param underlying
	 *            The underlying set of elements
	 */
	private ImmutableSet(final Set<E> underlying) {
		mUnderlying = Objects.requireNonNull(underlying);
		mHash = mUnderlying.hashCode();
	}

	/**
	 * Returns an empty, immutable set.
	 *
	 * @param <E>
	 *            The element type
	 * @return empty, immutable set
	 */
	public static <E> ImmutableSet<E> empty() {
		return new ImmutableSet<>(Collections.emptySet());
	}

	/**
	 * Creates a new immutable set, with the given underlying set of elements. The caller must guarantee to prevent any
	 * modification of the underlying set.
	 *
	 * This method automatically prevents instances of {@link ImmutableSet} from being nested.
	 *
	 * @param underlying
	 *            The underlying set of elements
	 * @return an immutable view of the given set
	 */
	public static <E> ImmutableSet<E> of(final Set<E> set) {
		if (set instanceof ImmutableSet<?>) {
			return (ImmutableSet<E>) set;
		}
		return new ImmutableSet<>(set);
	}

	/**
	 * Creates a new immutable set, with the given underlying set of elements. In contrast to
	 * {@link ImmutableSet#ImmutableSet(Set)}, a copy is made, and hence the caller can make modifications to the given
	 * set (that will not be reflected by the immutable copy).
	 *
	 * Beware that creating a copy of a set is performance-intensive. Thus, if a caller can guarantee that the given set
	 * will never be modified, it is recommended to use {@link #of(Set)} instead.
	 *
	 * If the given set is already immutable, it is returned immediately and no copy is made.
	 *
	 * @param <E>
	 *            The type of elements in the set
	 * @param set
	 *            The set of which an immutable copy is made.
	 * @return an immutable copy of the given set's current contents
	 */
	public static <E> ImmutableSet<E> copyOf(final Set<E> set) {
		if (set instanceof ImmutableSet<?>) {
			return (ImmutableSet<E>) set;
		}
		return new ImmutableSet<>(new HashSet<>(set));
	}

	@Override
	public boolean contains(final Object o) {
		return mUnderlying.contains(o);
	}

	@Override
	public boolean containsAll(final Collection<?> c) {
		return mUnderlying.containsAll(c);
	}

	@Override
	public boolean equals(final Object obj) {
		return mUnderlying.equals(obj);
	}

	@Override
	public int hashCode() {
		assert mUnderlying.hashCode() == mHash : "Immutable set was modified";
		return mHash;
	}

	@Override
	public boolean isEmpty() {
		return mUnderlying.isEmpty();
	}

	@Override
	public Iterator<E> iterator() {
		final Iterator<E> it = mUnderlying.iterator();
		return new Iterator<>() {
			@Override
			public boolean hasNext() {
				return it.hasNext();
			}

			@Override
			public E next() {
				return it.next();
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException(ERROR_MSG);
			}
		};
	}

	@Override
	public int size() {
		return mUnderlying.size();
	}

	@Override
	public Object[] toArray() {
		return mUnderlying.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] a) {
		return mUnderlying.toArray(a);
	}

	// Mutating methods below

	@Override
	public boolean add(final E e) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public boolean addAll(final Collection<? extends E> c) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public void clear() {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public boolean remove(final Object o) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public boolean removeIf(final Predicate<? super E> filter) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		throw new UnsupportedOperationException(ERROR_MSG);
	}
}
