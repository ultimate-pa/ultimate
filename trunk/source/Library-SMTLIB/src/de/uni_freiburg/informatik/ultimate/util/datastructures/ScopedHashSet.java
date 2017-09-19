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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;


public class ScopedHashSet<E> implements Set<E> {

	private final ScopedHashMap<E, Object> mBacking;
	
	public ScopedHashSet() {
		mBacking = new ScopedHashMap<E, Object>();
	}
	
	public void beginScope() {
		mBacking.beginScope();
	}
	
	public void endScope() {
		mBacking.endScope();
	}
	
	@Override
	public boolean add(E e) {
		return mBacking.put(e, this) == null;
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		boolean changed = false;
		for (final E e : c) {
			changed |= add(e);
		}
		return changed;
	}

	@Override
	public void clear() {
		mBacking.clear();
	}

	@Override
	public boolean contains(Object o) {
		return mBacking.get(o) == this;
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		for (final Object o : c) {
			if (!contains(o)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean isEmpty() {
		return mBacking.isEmpty();
	}
	
	public boolean isEmptyScope() {
		return mBacking.isEmptyScope();
	}

	@Override
	public Iterator<E> iterator() {
		return mBacking.keySet().iterator();
	}
	
	public Iterable<E> currentScope() {
		return mBacking.currentScopeKeys();
	}

	@Override
	public boolean remove(Object o) {
		return mBacking.remove(o) != null;
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		boolean res = false;
		for (final Object o : c) {
			res |= remove(o);
		}
		return res;
	}

	@Override
	public boolean retainAll(Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return mBacking.size();
	}

	@Override
	public Object[] toArray() {
		final Object [] res = new Object[size()];
		int pos = -1;
		final Iterator<E> it = iterator();
		while (it.hasNext()) {
			res[++pos] = it.next();
		}
		return res;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T> T[] toArray(T[] a) {
		final int s = size();
		final T[] res = a.length >= s ? a : Arrays.copyOf(a, s);
		int pos = -1;
		final Iterator<E> it = iterator();
		while (it.hasNext()) {
			res[++pos] = (T)it.next();
		}
		return res;
	}

	@Override
	public String toString() {
		return mBacking.keySet().toString();
	}
}
