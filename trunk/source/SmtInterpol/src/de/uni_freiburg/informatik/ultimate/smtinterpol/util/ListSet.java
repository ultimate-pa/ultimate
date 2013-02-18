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
import java.util.HashSet;
import java.util.Iterator;

/**
 * A scoped combination of a set and a list.  Elements are unique within this
 * collection (as in sets) and can be iterated in an order (as in lists).
 * 
 * Whenever a new scope is created, an empty list element is inserted into the
 * list (not into the set) and marks the beginning of this scope.  The scope is
 * unvisible for <code>ListSetIterator</code>, be can be retrieved using
 * <code>ScopeIterator</code>.  Note that scope iterators traverse only the top
 * most scope and in the opposite order of the input.
 * @author Juergen Christ
 */
public class ListSet<E> extends AbstractSet<E> {
	
	private class ScopeIterator implements Iterator<E> {
		ListSetElem<E> m_cur = m_root;
		@Override
		public boolean hasNext() {
			return m_cur.prev.elem != null;
		}

		@Override
		public E next() {
			m_cur = m_cur.prev;
			return m_cur.elem;
		}

		@Override
		public void remove() {
			m_cur = ListSet.this.remove(m_cur).next;
			ListSet.this.m_elems.remove(m_cur);
		}
		
	}
	
	public class ListSetIterator implements Iterator<E> {

		ListSetElem<E> m_cur;
		
		ListSetIterator(ListSetElem<E> cur) {
			m_cur = cur;
		}
		
		@Override
		public boolean hasNext() {
			ListSetElem<E> walk = m_cur.next;
			while (walk != m_root && walk.elem == null)
				walk = walk.next;
			return walk != m_root;
		}

		@Override
		public E next() {
			ListSetElem<E> walk = m_cur.next;
			while (walk != m_root && walk.elem == null)
				walk = walk.next;
			m_cur = walk;
			return m_cur.elem;
		}

		@Override
		public void remove() {
			m_cur = ListSet.this.remove(m_cur);
			ListSet.this.m_elems.remove(m_cur);
		}
		
	}
	
	private static class ListSetElem<E> {
		E elem;
		ListSetElem<E> next;
		ListSetElem<E> prev;
		public ListSetElem(E elem) {
			this.elem = elem;
			next = prev = this;
		}
		public int hashCode() {
			return elem == null ? 0 : elem.hashCode();
		}
		public boolean equals(Object other) {
			if (other instanceof ListSetElem<?>)
				other = ((ListSetElem<?>)other).elem;
			return elem == null ? other == null : elem.equals(other);
		}
	}
	
	private HashSet<ListSetElem<E>> m_elems;
	private ListSetElem<E> m_root;
	
	public ListSet() {
		m_elems = new HashSet<ListSetElem<E>>();
		m_root = new ListSetElem<E>(null);
	}
	
	public void beginScope() {
		ListSetElem<E> marker = new ListSetElem<E>(null);
		addToList(marker);
	}
	
	public void endScope() {
		ListSetElem<E> walk = m_root.prev;
		while (walk.elem != null) {
			m_elems.remove(walk);
			walk = remove(walk);
		}
	}
	
	private void addToList(ListSetElem<E> toAdd) {
		m_root.prev.next = toAdd;
		toAdd.next = m_root;
		toAdd.prev = m_root.prev;
		m_root.prev = toAdd;
	}
	
	public boolean add(E elem) {
		ListSetElem<E> toAdd = new ListSetElem<E>(elem);
		if (m_elems.add(toAdd)) {
			addToList(toAdd);
			return true;
		}
		return false;
	}

	// This iterator is not concurrent...
	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {

			Iterator<ListSetElem<E>> m_it = m_elems.iterator();
			ListSetElem<E> data;
			
			@Override
			public boolean hasNext() {
				return m_it.hasNext();
			}

			@Override
			public E next() {
				return (data = m_it.next()).elem;
			}

			@Override
			public void remove() {
				ListSet.this.remove(data);
				m_it.remove();
			}
			
		};
	}
	
	private ListSetElem<E> remove(ListSetElem<E> elem) {
		ListSetElem<E> prev = elem.prev;
		prev.next = elem.next;
		elem.next.prev = prev;
		elem.next = elem.prev = elem;
		// Don't do that since this method is called from the iterator
//		m_elems.remove(elem);
		return prev;
	}

	@Override
	public int size() {
		return m_elems.size();
	}
	
	public ListSetIterator listIterator() {
		return new ListSetIterator(m_root);
	}
	
	public ListSetIterator successors(ListSetIterator it) {
		return new ListSetIterator(it.m_cur);
	}
	
	public Iterator<E> scopeIterator() {
		return new ScopeIterator();
	}
	
	public Iterable<E> scope() {
		return new Iterable<E>() {

			@Override
			public Iterator<E> iterator() {
				return scopeIterator();
			}
			
		};
	}

}
