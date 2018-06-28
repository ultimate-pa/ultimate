/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * A {@link Deque} that does not contain duplicate instances. Whenever an object is added that is already present,
 * nothing happens instead.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <E>
 *            the elements of this {@link Deque}.
 */
public final class HashDeque<E> implements Deque<E> {
	private final Deque<E> mDeque;
	private final Set<E> mSet;

	public HashDeque() {
		mDeque = new ArrayDeque<>();
		mSet = new HashSet<>();
	}

	@Override
	public E pop() {
		final E node = mDeque.pop();
		mSet.remove(node);
		return node;
	}

	@Override
	public void push(final E node) {
		mDeque.push(node);
		final boolean modified = mSet.add(node);
		if (!modified) {
			throw new IllegalArgumentException("Illegal to add element twice " + node);
		}
	}

	@Override
	public boolean isEmpty() {
		return mSet.isEmpty();
	}

	@Override
	public Object[] toArray() {
		return mDeque.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] a) {
		return mDeque.toArray(a);
	}

	@Override
	public boolean containsAll(final Collection<?> c) {
		return mSet.containsAll(c);
	}

	@Override
	public boolean addAll(final Collection<? extends E> c) {
		boolean rtr = false;
		for (final E elem : c) {
			if (mSet.add(elem)) {
				mDeque.add(elem);
				rtr = true;
			}
		}
		return rtr;
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		final boolean rtr = mSet.removeAll(c);
		mDeque.removeAll(c);
		return rtr;
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		final boolean rtr = mSet.retainAll(c);
		mDeque.retainAll(c);
		return rtr;
	}

	@Override
	public void clear() {
		mSet.clear();
		mDeque.clear();
	}

	@Override
	public void addFirst(final E e) {
		if (mSet.add(e)) {
			mDeque.addFirst(e);
		}
	}

	@Override
	public void addLast(final E e) {
		if (mSet.add(e)) {
			mDeque.addLast(e);
		}
	}

	@Override
	public boolean offerFirst(final E e) {
		if (mSet.add(e)) {
			return mDeque.offerFirst(e);
		}
		return false;
	}

	@Override
	public boolean offerLast(final E e) {
		if (mSet.add(e)) {
			return mDeque.offerLast(e);
		}
		return false;
	}

	@Override
	public E removeFirst() {
		final E rtr = mDeque.removeFirst();
		mSet.remove(rtr);
		return rtr;
	}

	@Override
	public E removeLast() {
		final E rtr = mDeque.removeLast();
		mSet.remove(rtr);
		return rtr;
	}

	@Override
	public E pollFirst() {
		final E rtr = mDeque.pollFirst();
		if (rtr != null) {
			mSet.remove(rtr);
		}
		return rtr;
	}

	@Override
	public E pollLast() {
		final E rtr = mDeque.pollLast();
		if (rtr != null) {
			mSet.remove(rtr);
		}
		return rtr;
	}

	@Override
	public E getFirst() {
		return mDeque.getFirst();
	}

	@Override
	public E getLast() {
		return mDeque.getLast();
	}

	@Override
	public E peekFirst() {
		return mDeque.peekFirst();
	}

	@Override
	public E peekLast() {
		return mDeque.peekLast();
	}

	@Override
	public boolean removeFirstOccurrence(final Object o) {
		if (mSet.remove(o)) {
			return mDeque.removeFirstOccurrence(o);
		}
		return false;
	}

	@Override
	public boolean removeLastOccurrence(final Object o) {
		if (mSet.remove(o)) {
			return mDeque.removeLastOccurrence(o);
		}
		return false;
	}

	@Override
	public boolean add(final E e) {
		if (mSet.add(e)) {
			return mDeque.add(e);
		}
		return false;
	}

	@Override
	public boolean offer(final E e) {
		if (mSet.add(e)) {
			return mDeque.offer(e);
		}
		return false;
	}

	@Override
	public E remove() {
		final E rtr = mDeque.remove();
		mSet.remove(rtr);
		return rtr;
	}

	@Override
	public E poll() {
		final E rtr = mDeque.poll();
		mSet.remove(rtr);
		return rtr;
	}

	@Override
	public E element() {
		return mDeque.element();
	}

	@Override
	public E peek() {
		return mDeque.peek();
	}

	@Override
	public boolean remove(final Object o) {
		if (mSet.remove(o)) {
			return mDeque.remove(o);
		}
		return false;
	}

	@Override
	public boolean contains(final Object o) {
		return mSet.contains(o);
	}

	@Override
	public int size() {
		return mSet.size();
	}

	@Override
	public Iterator<E> iterator() {
		return mDeque.iterator();
	}

	@Override
	public Iterator<E> descendingIterator() {
		return mDeque.descendingIterator();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDeque == null) ? 0 : mDeque.hashCode());
		return result;
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
		final HashDeque<?> other = (HashDeque<?>) obj;
		if (mDeque == null) {
			if (other.mDeque != null) {
				return false;
			}
		} else if (!mDeque.equals(other.mDeque)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return mDeque.toString();
	}

}