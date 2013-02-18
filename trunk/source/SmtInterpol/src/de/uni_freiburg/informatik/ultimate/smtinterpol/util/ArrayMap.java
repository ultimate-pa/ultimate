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

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public class ArrayMap<K, V> extends AbstractMap<K, V> {

	private K[] m_keys;
	private V[] m_values;
	public ArrayMap(K[] keys,V[] values){
		if (keys.length != values.length)
			throw new IllegalArgumentException("Unequal array lengths");
		m_keys = keys;
		m_values = values;
	}
	private class ArrayMapEntry implements Map.Entry<K, V> {
		private int m_id;
		public ArrayMapEntry(int id) {
			m_id = id;
		}
		@Override
		public K getKey() {
			return m_keys[m_id];
		}

		@Override
		public V getValue() {
			return m_values[m_id];
		}

		@Override
		public V setValue(V value) {
			V old = m_values[m_id];
			m_values[m_id] = value;
			return old;
		}
		
	}
	@Override
	public Set<java.util.Map.Entry<K, V>> entrySet() {
		return new AbstractSet<Entry<K,V>>() {

			@Override
			public Iterator<java.util.Map.Entry<K, V>> iterator() {
				return new Iterator<java.util.Map.Entry<K, V>>() {
					private int m_id = 0;

					@Override
					public boolean hasNext() {
						return m_id < m_keys.length;
					}

					@Override
					public java.util.Map.Entry<K, V> next() {
						return new ArrayMapEntry(m_id++);
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException("No remove!");
					}
					
				};
			}

			@Override
			public int size() {
				return m_keys.length;
			}
			
		};
	}

}
