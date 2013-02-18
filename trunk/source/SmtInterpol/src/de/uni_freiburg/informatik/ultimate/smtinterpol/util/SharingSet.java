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
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class SharingSet<E> extends AbstractSet<E> {
	
	private static final class SharingSetData<E> {
		SharingSetData() {
			m_Rep = new HashSet<E>();
			m_Sharing = 0;
		}
		SharingSetData(SharingSetData<E> other) {
			m_Rep = new HashSet<E>(other.m_Rep);
			m_Sharing = 0;
		}
		SharingSetData(E obj) {
			m_Rep = Collections.singleton(obj);
			// HACK: The first write modification has to copy the map since it
			//       is immutable...
			m_Sharing = 1;
		}
		Set<E> m_Rep;
		// XXX Should this be atomic for multi threading support
		// Currently, we do not support multiple threads!!!
		int m_Sharing;
		SharingSetData<E> share() {
			++m_Sharing;
			return this;
		}
		SharingSetData<E> detach() {
			if (m_Sharing != 0) {
				// one shared access less
				--m_Sharing;
				return new SharingSetData<E>(this);
			}
			return this;
		}
	}
	
	private SharingSetData<E> m_Data;
	
	public SharingSet() {
		m_Data = new SharingSetData<E>();
	}
	
	public SharingSet(SharingSet<E> other) {
		m_Data = other.m_Data.share();
	}
	// UNMODIFIABLE sharing set...
	public SharingSet(E obj) {
		m_Data = new SharingSetData<E>(obj);
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			Iterator<E> sink = m_Data.m_Rep.iterator();
			@Override
			public boolean hasNext() {
				return sink.hasNext();
			}

			@Override
			public E next() {
				return sink.next();
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("remove not allowed on SharingSet iterator");
			}
			
		};
	}

	@Override
	public int size() {
		return m_Data.m_Rep.size();
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		SharingSetData<E> data = m_Data.detach();
		boolean res = data.m_Rep.removeAll(c);
		if (res)
			m_Data = data;
		return res;
	}

	@Override
	public boolean add(E e) {
		if (m_Data.m_Rep.contains(e))
			return false;
		m_Data = m_Data.detach();
		return m_Data.m_Rep.add(e);
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		if (m_Data.m_Rep.containsAll(c))
			return false;
		m_Data = m_Data.detach();
		return m_Data.m_Rep.addAll(c);
	}
	// Optimization for sharing sets...
	public boolean addShared(SharingSet<E> other) {
		if (other == null)
			return false;
		if (m_Data.m_Rep.isEmpty() && m_Data.m_Sharing == 0) {
			m_Data = other.m_Data.share();
			return true;
		}
		return addAll(other.m_Data.m_Rep);
	}

	@Override
	public boolean contains(Object o) {
		return m_Data.m_Rep.contains(o);
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		return m_Data.m_Rep.containsAll(c);
	}

	@Override
	public boolean remove(Object o) {
		if (m_Data.m_Rep.contains(o)) {
			m_Data = m_Data.detach();
			return m_Data.m_Rep.remove(o);
		}
		return false;
	}

}
