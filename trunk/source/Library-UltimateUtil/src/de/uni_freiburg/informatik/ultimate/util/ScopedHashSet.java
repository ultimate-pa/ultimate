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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;


public class ScopedHashSet<E> implements Set<E> {

	private ScopedHashMap<E, Object> m_Backing;
	
	public ScopedHashSet() {
		m_Backing = new ScopedHashMap<E, Object>();
	}
	
	public void beginScope() {
		m_Backing.beginScope();
	}
	
	public void endScope() {
		m_Backing.endScope();
	}
	
	@Override
	public boolean add(E e) {
		return m_Backing.put(e, this) == null;
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		boolean changed = false;
		for (E e : c) {
			changed |= add(e);
		}
		return changed;
	}

	@Override
	public void clear() {
		m_Backing.clear();
	}

	@Override
	public boolean contains(Object o) {
		return m_Backing.get(o) == this;
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		for (Object o : c) {
			if (!contains(o))
				return false;
		}
		return true;
	}

	@Override
	public boolean isEmpty() {
		return m_Backing.isEmpty();
	}
	
	public boolean isEmptyScope() {
		return m_Backing.isEmptyScope();
	}

	@Override
	public Iterator<E> iterator() {
		return m_Backing.keySet().iterator();
	}
	
	public Iterable<E> currentScope() {
		return m_Backing.currentScopeKeys();
	}

	@Override
	public boolean remove(Object o) {
		return m_Backing.remove(o) != null;
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		boolean res = false;
		for (Object o : c)
			res |= remove(o);
		return res;
	}

	@Override
	public boolean retainAll(Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return m_Backing.size();
	}

	@Override
	public Object[] toArray() {
		Object [] res = new Object[size()];
		int pos = -1;
		Iterator<E> it = iterator();
		while (it.hasNext())
			res[++pos] = it.next();
		return res;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T> T[] toArray(T[] a) {
		int s = size();
		T[] res = a.length >= s ? a : Arrays.copyOf(a, s);
		int pos = -1;
		Iterator<E> it = iterator();
		while (it.hasNext())
			res[++pos] = (T)it.next();
		return res;
	}

	public String toString() {
		return m_Backing.keySet().toString();
	}
}
