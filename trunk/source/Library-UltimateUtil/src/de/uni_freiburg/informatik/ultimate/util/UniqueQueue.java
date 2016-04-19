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
package de.uni_freiburg.informatik.ultimate.util;

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
 * @author Daniel Tischner
 *
 * @param <T>
 *            Class of objects the queue should contain
 */
public final class UniqueQueue<T> implements Queue<T> {
	/**
	 * Queue used by the element.
	 */
	private final Queue<T> m_Queue;
	/**
	 * Set used by the element to ensure uniqueness of elements.
	 */
	private final Set<T> m_Set;

	/**
	 * Creates a new empty unique queue element.
	 */
	public UniqueQueue() {
		m_Queue = new LinkedList<>();
		m_Set = new HashSet<>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#add(java.lang.Object)
	 */
	@Override
	public boolean add(final T e) {
		boolean changed = m_Set.add(e);
		if (changed) {
			m_Queue.add(e);
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
		for (T e : c) {
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
		m_Set.clear();
		m_Queue.clear();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#contains(java.lang.Object)
	 */
	@Override
	public boolean contains(final Object o) {
		return m_Set.contains(o);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#containsAll(java.util.Collection)
	 */
	@Override
	public boolean containsAll(final Collection<?> c) {
		return m_Set.containsAll(c);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#element()
	 */
	@Override
	public T element() {
		return m_Queue.element();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return m_Set.isEmpty();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#iterator()
	 */
	@Override
	public Iterator<T> iterator() {
		return m_Queue.iterator();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#offer(java.lang.Object)
	 */
	@Override
	public boolean offer(final T e) {
		boolean changed = m_Queue.offer(e);
		if (changed) {
			m_Set.add(e);
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
		return m_Queue.peek();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#poll()
	 */
	@Override
	public T poll() {
		T element = m_Queue.poll();
		m_Set.remove(element);
		return element;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Queue#remove()
	 */
	@Override
	public T remove() {
		T element = m_Queue.remove();
		m_Set.remove(element);
		return element;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#remove(java.lang.Object)
	 */
	@Override
	public boolean remove(Object o) {
		boolean changed = m_Set.remove(o);
		if (changed) {
			m_Queue.remove(o);
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
		boolean changed = m_Set.removeAll(c);
		if (changed) {
			m_Queue.removeAll(c);
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
		boolean changed = m_Set.retainAll(c);
		if (changed) {
			m_Queue.retainAll(c);
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
		return m_Queue.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#toArray()
	 */
	@Override
	public Object[] toArray() {
		return m_Queue.toArray();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.util.Collection#toArray(java.lang.Object[])
	 */
	@Override
	public <K> K[] toArray(final K[] a) {
		return m_Queue.toArray(a);
	}

}
