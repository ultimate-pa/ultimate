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

	private final IdentityHashMap<E, Object> mBacking;
	
	public IdentityHashSet() {
		mBacking = new IdentityHashMap<E, Object>();
	}
	
	@Override
	public Iterator<E> iterator() {
		return mBacking.keySet().iterator();
	}

	@Override
	public int size() {
		return mBacking.size();
	}

	@Override
	public boolean contains(Object o) {
		return mBacking.containsKey(o);
	}

	@Override
	public boolean add(E e) {
		return mBacking.put(e, this) == null;
	}

	@Override
	public boolean remove(Object o) {
		return mBacking.remove(o) != null;
	}

	@Override
	public void clear() {
		mBacking.clear();
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		boolean changed = false;
		for (final Object o : c) {
			changed |= remove(o);
		}
		return changed;
	}

}
