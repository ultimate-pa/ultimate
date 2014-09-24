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
import java.util.Map;
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

}
