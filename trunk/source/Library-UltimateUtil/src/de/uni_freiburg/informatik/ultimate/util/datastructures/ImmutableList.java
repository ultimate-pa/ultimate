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

import java.util.AbstractSequentialList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.NoSuchElementException;
import java.util.Objects;

/**
 * Implements an immutable LISP-like list. Multiple instances can share common suffixes.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <X>
 *            The type of elements in the list.
 */
public final class ImmutableList<X> extends AbstractSequentialList<X> {
	@SuppressWarnings("rawtypes")
	private static final ImmutableList NIL = new ImmutableList<>();

	private final int mSize;
	private final X mHead;
	private final ImmutableList<X> mTail;

	// NIL constructor
	private ImmutableList() {
		mSize = 0;
		mHead = null;
		mTail = null;
	}

	/**
	 * CONS constructor: creates a new list that prepends an element to the given list.
	 *
	 * @param head
	 *            The head element of the list.
	 * @param tail
	 *            The list tail (must not be null).
	 */
	public ImmutableList(final X head, final ImmutableList<X> tail) {
		mSize = tail.mSize + 1;
		mHead = head;
		mTail = Objects.requireNonNull(tail);
	}

	/**
	 * Creates a list with the given elements. Does not share memory with other lists.
	 *
	 * @param elements
	 *            The elements of the list, in order.
	 */
	@SafeVarargs
	public ImmutableList(final X... elements) {
		this(Arrays.stream(elements).iterator());
	}

	/**
	 * Creates a list with the given elements. Does not share memory with other lists.
	 *
	 * @param elements
	 *            The elements of the list, in order.
	 */
	public ImmutableList(final Collection<X> elements) {
		this(elements.iterator());
	}

	private ImmutableList(final Iterator<X> it) {
		if (it.hasNext()) {
			mHead = it.next();
			mTail = it.hasNext() ? new ImmutableList<>(it) : empty();
			mSize = mTail.mSize + 1;
		} else {
			mHead = null;
			mTail = null;
			mSize = 0;
		}
	}

	/**
	 * Returns the empty list (NIL).
	 *
	 * @param <X>
	 *            The element type
	 * @return an empty list
	 */
	@SuppressWarnings("unchecked")
	public static <X> ImmutableList<X> empty() {
		return NIL;
	}

	/**
	 * Creates a singleton list.
	 *
	 * @param <X>
	 *            The element type
	 * @param elem
	 *            The single element in the list
	 * @return the new list
	 */
	public static <X> ImmutableList<X> singleton(final X elem) {
		return new ImmutableList<>(elem, empty());
	}

	public X getHead() {
		if (mSize == 0) {
			throw new NoSuchElementException();
		}
		return mHead;
	}

	public ImmutableList<X> getTail() {
		if (mSize == 0) {
			throw new UnsupportedOperationException();
		}
		return mTail;
	}

	@Override
	public int hashCode() {
		// Super class properly implements List#hashCode().
		return super.hashCode();
	}

	@Override
	public boolean equals(final Object o) {
		// Optimizations over super.equals():
		if (o == this) {
			return true;
		}
		if (o instanceof ImmutableList<?>) {
			final ImmutableList<?> other = (ImmutableList<?>) o;
			if (mSize != other.mSize) {
				return false;
			}
			if (mTail == other.mTail) {
				return Objects.equals(mHead, other.mHead);
			}
		}

		// Super class properly implements List#equals().
		return super.equals(o);
	}

	@Override
	public int size() {
		return mSize;
	}

	@Override
	public boolean add(final X e) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean remove(final Object o) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAll(final Collection<? extends X> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAll(final int index, final Collection<? extends X> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void clear() {
		throw new UnsupportedOperationException();
	}

	@Override
	public X set(final int index, final X element) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void add(final int index, final X element) {
		throw new UnsupportedOperationException();
	}

	@Override
	public X remove(final int index) {
		throw new UnsupportedOperationException();
	}

	@Override
	public ListIterator<X> listIterator(final int index) {
		if (index < 0 || index > mSize) {
			throw new IndexOutOfBoundsException();
		}

		int currentIndex = index;
		ImmutableList<X> current = this;
		while (currentIndex > 0) {
			current = current.mTail;
			currentIndex--;
		}

		return new ConsListIterator<>(current, currentIndex);
	}

	private static final class ConsListIterator<X> implements ListIterator<X> {
		private ImmutableList<X> mCurrent;
		private int mIndex;

		public ConsListIterator(final ImmutableList<X> list, final int index) {
			mCurrent = list;
			mIndex = index;
		}

		@Override
		public boolean hasNext() {
			return mCurrent != null && mCurrent.mSize > 0;
		}

		@Override
		public X next() {
			if (mCurrent == null || mCurrent.mSize == 0) {
				throw new NoSuchElementException();
			}
			final X elem = mCurrent.mHead;
			mCurrent = mCurrent.mTail;
			mIndex++;
			return elem;
		}

		@Override
		public boolean hasPrevious() {
			throw new UnsupportedOperationException();
		}

		@Override
		public X previous() {
			throw new UnsupportedOperationException();
		}

		@Override
		public int nextIndex() {
			return mIndex;
		}

		@Override
		public int previousIndex() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void set(final X e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void add(final X e) {
			throw new UnsupportedOperationException();
		}
	}
}
