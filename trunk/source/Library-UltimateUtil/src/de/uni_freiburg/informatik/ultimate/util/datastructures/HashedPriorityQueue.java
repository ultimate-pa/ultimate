/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 *
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * A {@link PriorityQueue} that additionally hashes its contents s.t. the {@link #contains(Object)} operation performs
 * in O(1).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <E>
 */
public class HashedPriorityQueue<E> implements Queue<E>, Set<E>, Collection<E> {
	private final Queue<E> mQueue;
	private final Set<E> mSet;

	public HashedPriorityQueue(final Comparator<E> comp) {
		mQueue = new PriorityQueue<>(comp);
		mSet = new HashSet<>();
	}

	/**
	 * Tries to find an element of this queue with the same hash as the supplied element.
	 *
	 * @param obj
	 *            An object for which you want to find a corresponding object in this queue.
	 * @return An element of this queue with the same hash as <tt>obj</tt> or null.
	 */
	public E find(final Object obj) {
		if (obj == null) {
			return null;
		}
		final int hash = obj.hashCode();
		final Iterator<E> iter = mQueue.iterator();
		while (iter.hasNext()) {
			final E current = iter.next();
			if (current.hashCode() == hash) {
				return current;
			}
		}
		return null;
	}

	@Override
	public boolean remove(final Object successor) {
		if (mQueue.remove(successor)) {
			mSet.remove(successor);
			return true;
		}
		return false;
	}

	@Override
	public E poll() {
		final E rtr = mQueue.poll();
		mSet.remove(rtr);
		return rtr;
	}

	@Override
	public boolean isEmpty() {
		return mQueue.isEmpty();
	}

	@Override
	public boolean add(final E elem) {
		if (mSet.add(elem)) {
			mQueue.add(elem);
			return true;
		}
		return false;
	}

	@Override
	public boolean contains(final Object obj) {
		return mSet.contains(obj);
	}

	@Override
	public String toString() {
		return Utils.join(mQueue, ", ");
	}

	@Override
	public int size() {
		return mSet.size();
	}

	@Override
	public Iterator<E> iterator() {
		return mQueue.iterator();
	}

	@Override
	public Object[] toArray() {
		return mQueue.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] a) {
		return mQueue.toArray(a);
	}

	@Override
	public boolean containsAll(final Collection<?> c) {
		return mSet.containsAll(c);
	}

	@Override
	public boolean addAll(final Collection<? extends E> c) {
		if (mSet.addAll(c)) {
			mQueue.addAll(c);
			return true;
		}
		return false;
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		if (mSet.removeAll(c)) {
			mQueue.removeAll(c);
			return true;
		}
		return false;
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		if (mSet.retainAll(c)) {
			mQueue.retainAll(c);
			return true;
		}
		return false;
	}

	@Override
	public void clear() {
		mSet.clear();
		mQueue.clear();
	}

	@Override
	public boolean offer(final E e) {
		return add(e);
	}

	@Override
	public E remove() {
		final E removed = mQueue.remove();
		mSet.remove(removed);
		return removed;
	}

	@Override
	public E element() {
		return mQueue.element();
	}

	@Override
	public E peek() {
		return mQueue.peek();
	}
}
