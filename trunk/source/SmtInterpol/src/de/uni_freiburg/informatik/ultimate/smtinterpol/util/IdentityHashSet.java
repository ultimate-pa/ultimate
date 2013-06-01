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
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;

public class IdentityHashSet<E> extends AbstractSet<E> {

	private IdentityHashMap<E, Object> m_Backing;
	
	public IdentityHashSet() {
		m_Backing = new IdentityHashMap<E, Object>();
	}
	
	@Override
	public Iterator<E> iterator() {
		return m_Backing.keySet().iterator();
	}

	@Override
	public int size() {
		return m_Backing.size();
	}

	@Override
	public boolean contains(Object o) {
		return m_Backing.containsKey(o);
	}

	@Override
	public boolean add(E e) {
		return m_Backing.put(e, this) == null;
	}

	@Override
	public boolean remove(Object o) {
		return m_Backing.remove(o) != null;
	}

	@Override
	public void clear() {
		m_Backing.clear();
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		boolean changed = false;
		for (Object o : c)
			changed |= remove(o);
		return changed;
	}

}
