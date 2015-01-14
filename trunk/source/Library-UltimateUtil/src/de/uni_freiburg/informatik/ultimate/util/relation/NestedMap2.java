/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.relation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Map.Entry;
import java.util.Set;

/**
 * TODO: comment
 * @author Matthias Heizmann
 *
 * @param <K1>
 * @param <K2>
 * @param <V>
 */
public class NestedMap2<K1, K2, V> {
	
	private final Map<K1, Map<K2, V>> m_K1ToK2ToV = new HashMap<K1, Map<K2, V>>();
	
	public V put(K1 key1, K2 key2, V value) {
		Map<K2, V> k2toV = m_K1ToK2ToV.get(key1);
		if (k2toV == null) {
			k2toV = new HashMap<>();
			m_K1ToK2ToV.put(key1, k2toV);
		}
		return k2toV.put(key2, value);
	}
	
	public V get(K1 key1, K2 key2) {
		Map<K2, V> k2toV = m_K1ToK2ToV.get(key1);
		if (k2toV == null) {
			return null;
		} else {
			return k2toV.get(key2);
		}
	}
	
	public Map<K2,V> get(K1 key1) {
		return m_K1ToK2ToV.get(key1);
	}
	
	public Set<K1> keySet() {
		return m_K1ToK2ToV.keySet();
	}
	
	public Iterable<Pair<K1,K2>> keys2() {
		return new Iterable<Pair<K1,K2>>() {

			@Override
			public Iterator<Pair<K1, K2>> iterator() {
				return new Iterator<Pair<K1,K2>>() {
					private Iterator<Entry<K1, Map<K2, V>>> m_Iterator1;
					private Entry<K1, Map<K2, V>> m_Iterator1Object;
					private Iterator<K2> m_Iterator2;

					{
						m_Iterator1 = m_K1ToK2ToV.entrySet().iterator();
						if (m_Iterator1.hasNext()) {
							m_Iterator1Object = m_Iterator1.next();
							m_Iterator2 = m_Iterator1Object.getValue().keySet().iterator();
						}
					}

					@Override
					public boolean hasNext() {
						if (m_Iterator1Object == null) {
							return false;
						} else {
							return m_Iterator2.hasNext();
						}
					}

					@Override
					public Pair<K1, K2> next() {
						if (m_Iterator1Object == null) {
							throw new NoSuchElementException();
						} else {
							if (!m_Iterator2.hasNext()) {
								if (!m_Iterator1.hasNext()) {
									throw new NoSuchElementException();
								} else {
									m_Iterator1Object = m_Iterator1.next();
									assert m_Iterator1Object.getValue().size() > 0 : "must contain at least one value";
									m_Iterator2 = m_Iterator1Object.getValue().keySet().iterator();
								}
							}
							return new Pair<K1, K2>(m_Iterator1Object.getKey(), m_Iterator2.next());
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException("not yet implemented");
					}
				};
			}
		};
		
	}
	
	//TODO more efficient iterable
	public Iterable<Triple<K1,K2,V>> entrySet() {
		ArrayList<Triple<K1,K2,V>> result = new ArrayList<Triple<K1,K2,V>>();
		for (Entry<K1, Map<K2, V>> entryOuter  : m_K1ToK2ToV.entrySet()) {
			for (Entry<K2, V> entryInner : entryOuter.getValue().entrySet()) {
				result.add(new Triple<>(entryOuter.getKey(), entryInner.getKey(), entryInner.getValue()));
			}
		}
		return result;
	}

	public void addAll(NestedMap2<K1, K2, V> nestedMap) {
		for (Triple<K1, K2, V> triple : nestedMap.entrySet()) {
			this.put(triple.getFirst(), triple.getSecond(), triple.getThird());
		}
	}
	
	public Map<K2, V> remove(K1 k1) {
		return m_K1ToK2ToV.remove(k1);
	}
	
	public V remove(K1 k1, K2 k2) {
		Map<K2, V> k2ToV = m_K1ToK2ToV.get(k1);
		if (k2ToV == null) {
			return null;
		} else {
			return k2ToV.remove(k2);
		}
	}

	@Override
	public String toString() {
		return m_K1ToK2ToV.toString();
	}
	
	

}
