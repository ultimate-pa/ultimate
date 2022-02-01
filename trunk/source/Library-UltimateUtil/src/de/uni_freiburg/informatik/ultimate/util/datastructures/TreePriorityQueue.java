/*
 * Copyright (C) 2019 Mehdi Naouar
 * Copyright (C) 2019 University of Freiburg
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
import java.util.Comparator;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * A TreeSet-based implementation of a priority queue. This queue can only be used if the Queue order is total.
 * The main advantage of this queue is that the time complexity of remove(o) is logarithmic
 *
 * @author Mehdi Naouar
 *
 */
public class TreePriorityQueue<E> implements Queue<E> {
	private final TreeSet<E> mQueue;
	
	public TreePriorityQueue() {
		mQueue = new TreeSet<>();
	}
	public TreePriorityQueue(Comparator<E> comp) {
		mQueue = new TreeSet<>(comp);
	}
	public TreePriorityQueue(Collection<E> col) {
		mQueue = new TreeSet<>(col);
	}
	public TreePriorityQueue(SortedSet<E> s) {
		mQueue = new TreeSet<>(s);
	}

	@Override
	public boolean addAll(final Collection<? extends E> c) {
		return mQueue.addAll(c);
	}

	@Override
	public void clear() {
		mQueue.clear();
	}

	@Override
	public boolean contains(final Object o) {
		return mQueue.contains(o);
	}

	@Override
	public boolean containsAll(final Collection<?> c) {
		return mQueue.containsAll(c);
	}

	@Override
	public boolean isEmpty() {
		return mQueue.isEmpty();
	}

	@Override
	public Iterator<E> iterator() {
		return mQueue.iterator();
	}

	@Override
	public boolean remove(final Object o) {
		return mQueue.remove(o);
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		return mQueue.removeAll(c);
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		return mQueue.retainAll(c);
	}

	@Override
	public int size() {
		return mQueue.size();
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
	public boolean add(final E arg0) {
		return mQueue.add(arg0);
	}

	@Override
	public E element() {
		return mQueue.first();
	}

	@Override
	public boolean offer(final E e) {
		return mQueue.add(e);
	}

	@Override
	public E peek() {
		if (mQueue.isEmpty()) {
			return null;
		} else {
			return mQueue.first();
		}
	}

	@Override
	public E poll() {
		return mQueue.pollFirst();
	}

	@Override
	public E remove() {
		if (mQueue.isEmpty()) {
			throw new NoSuchElementException("The Queue is Empty");
		}
		return mQueue.pollFirst();
	}
}
