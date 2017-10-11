/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

/**
 * Nested map that stores a value accessible by 5 different keys.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <K1>
 *            First key
 * @param <K2>
 *            Second key
 * @param <K3>
 *            Third key
 * @param <K4>
 *            Fourth key
 * @param <K5>
 *            Fifth key
 * @param <V>
 *            Value
 */
public class NestedMap5<K1, K2, K3, K4, K5, V> {

	/**
	 * Internal map that adds the first key to a {@link NestedMap4}.
	 */
	private final Map<K1, NestedMap4<K2, K3, K4, K5, V>> mK1ToK2ToK3ToK4ToK5V = new HashMap<K1, NestedMap4<K2, K3, K4, K5, V>>();

	/**
	 * Clears the nested map.
	 */
	public void clear() {
		mK1ToK2ToK3ToK4ToK5V.clear();
	}
	
	/**
	 * Returns a stream to all values of the nested map.
	 * 
	 * @return A stream to all values of the nested map
	 */
	public Stream<V> values() {
		return this.mK1ToK2ToK3ToK4ToK5V.values().stream().flatMap(NestedMap4::values);
	}

	/**
	 * Gets the value that is stored at the given position.
	 * 
	 * @param key1
	 *            First key where the value is stored
	 * @param key2
	 *            Second key where the value is stored
	 * @param key3
	 *            Third key where the value is stored
	 * @param key4
	 *            Fourth key where the value is stored
	 * @param key5
	 *            Fifth key where the value is stored
	 * @return The value stored at the given position.
	 */
	public V get(K1 key1, K2 key2, K3 key3, K4 key4, K5 key5) {
		final NestedMap4<K2, K3, K4, K5, V> k2tok3tok4tok5toV = mK1ToK2ToK3ToK4ToK5V.get(key1);
		if (k2tok3tok4tok5toV == null) {
			return null;
		} else {
			return k2tok3tok4tok5toV.get(key2, key3, key4, key5);
		}
	}

	/**
	 * Puts the given value in the nested map. See
	 * {@link Map#put(Object, Object)}.
	 * 
	 * @param key1
	 *            First key to store the value at
	 * @param key2
	 *            Second key to store the value at
	 * @param key3
	 *            Third key to store the value at
	 * @param key4
	 *            Fourth key to store the value at
	 * @param key5
	 *            Fifth key to store the value at
	 * @param value
	 *            Value to store
	 * @return The previous value associated with key, or <tt>null</tt> if there
	 *         was no mapping for key. See {@link Map#put(Object, Object)}.
	 */
	public V put(K1 key1, K2 key2, K3 key3, K4 key4, K5 key5, V value) {
		NestedMap4<K2, K3, K4, K5, V> k2tok3tok4tok5toV = mK1ToK2ToK3ToK4ToK5V.get(key1);
		if (k2tok3tok4tok5toV == null) {
			k2tok3tok4tok5toV = new NestedMap4<>();
			mK1ToK2ToK3ToK4ToK5V.put(key1, k2tok3tok4tok5toV);
		}
		return k2tok3tok4tok5toV.put(key2, key3, key4, key5, value);
	}
}
