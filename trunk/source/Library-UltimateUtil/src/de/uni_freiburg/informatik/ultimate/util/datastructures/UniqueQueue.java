/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2015 University of Freiburg
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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

/**
 * Queue object which ensures uniqueness of elements. An element will only be
 * added if it was not already contained in the queue. This combines the
 * strengths of {@link Queue} and {@link Set}. The disadvantage is that the
 * queue must also maintain a set, thus time and space complexity increases.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <T>
 *            Class of objects the queue should contain
 */
public final class UniqueQueue<T> implements Queue<T> {
	/**
	 * Queue used by the element.
	 */
	private final Queue<T> mQueue;
	/**
	 * Set used by the element to ensure uniqueness of elements.
	 */
	private final Set<T> mSet;

	/**
	 * Creates a new empty unique queue element.
	 */
	public UniqueQueue() {
		mQueue = new LinkedList<>();
		mSet = new HashSet<>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#add(java.lang.Object)
	 */
	@Override
	public boolean add(final T e) {
		final boolean changed = mSet.add(e);
		if (changed) {
			mQueue.add(e);
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#addAll(java.util.Collection)
	 */
	@Override
	public boolean addAll(final Collection<? extends T> c) {
		boolean changed = false;
		for (final T e : c) {
			if (add(e)) {
				changed = true;
			}
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#clear()
	 */
	@Override
	public void clear() {
		mSet.clear();
		mQueue.clear();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#contains(java.lang.Object)
	 */
	@Override
	public boolean contains(final Object o) {
		return mSet.contains(o);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#containsAll(java.util.Collection)
	 */
	@Override
	public boolean containsAll(final Collection<?> c) {
		return mSet.containsAll(c);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#element()
	 */
	@Override
	public T element() {
		return mQueue.element();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return mSet.isEmpty();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#iterator()
	 */
	@Override
	public Iterator<T> iterator() {
		return mQueue.iterator();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#offer(java.lang.Object)
	 */
	@Override
	public boolean offer(final T e) {
		final boolean changed = mQueue.offer(e);
		if (changed) {
			mSet.add(e);
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#peek()
	 */
	@Override
	public T peek() {
		return mQueue.peek();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#poll()
	 */
	@Override
	public T poll() {
		final T element = mQueue.poll();
		mSet.remove(element);
		return element;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#remove()
	 */
	@Override
	public T remove() {
		final T element = mQueue.remove();
		mSet.remove(element);
		return element;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#remove(java.lang.Object)
	 */
	@Override
	public boolean remove(Object o) {
		final boolean changed = mSet.remove(o);
		if (changed) {
			mQueue.remove(o);
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#removeAll(java.util.Collection)
	 */
	@Override
	public boolean removeAll(final Collection<?> c) {
		final boolean changed = mSet.removeAll(c);
		if (changed) {
			mQueue.removeAll(c);
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#retainAll(java.util.Collection)
	 */
	@Override
	public boolean retainAll(final Collection<?> c) {
		final boolean changed = mSet.retainAll(c);
		if (changed) {
			mQueue.retainAll(c);
		}
		return changed;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#size()
	 */
	@Override
	public int size() {
		return mQueue.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#toArray()
	 */
	@Override
	public Object[] toArray() {
		return mQueue.toArray();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#toArray(java.lang.Object[])
	 */
	@Override
	public <K> K[] toArray(final K[] a) {
		return mQueue.toArray(a);
	}

}
