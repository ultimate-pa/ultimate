/*
 * Copyright (C) 2015-2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Allows to construct objects lazily. Stores a Map from keys to values. The getOrConstruct methods will return the
 * value for a given key if the value was already constructed. If the the value was not already constructed it is
 * constructed at the first call of the getOrConstruct method. Construction of elements is done by Objects that
 * implement this IValueConstruction interface of this class.
 *
 * Note that this cache does not support null values, i.e., it cannot cache them.
 *
 * @author Matthias Heizmann
 *
 */
public class ConstructionCache<K, V> implements Map<K, V> {
	private final Map<K, V> mMap;
	private final IValueConstruction<K, V> mValueComputation;

	public ConstructionCache(final IValueConstruction<K, V> valueConstruction, final Map<K, V> backing) {
		mValueComputation = valueConstruction;
		mMap = backing;
	}

	public ConstructionCache(final IValueConstruction<K, V> valueConstruction) {
		this(valueConstruction, new HashMap<>());
	}

	/**
	 * Get value stored for key. Construct value if not already constructed.
	 */
	public V getOrConstruct(final K key) {
		V value = mMap.get(key);
		if (value == null) {
			value = mValueComputation.constructValue(key);
			mMap.put(key, value);
		}
		return value;
	}

	@Override
	public int size() {
		return mMap.size();
	}

	@Override
	public boolean isEmpty() {
		return mMap.isEmpty();
	}

	@Override
	public boolean containsKey(final Object key) {
		return mMap.containsKey(key);
	}

	@Override
	public boolean containsValue(final Object value) {
		return mMap.containsValue(value);
	}

	@Override
	public V get(final Object key) {
		return mMap.get(key);
	}

	@Override
	public V put(final K key, final V value) {
		return mMap.put(key, value);
	}

	@Override
	public V remove(final Object key) {
		return mMap.remove(key);
	}

	@Override
	public void putAll(final Map<? extends K, ? extends V> m) {
		mMap.putAll(m);
	}

	@Override
	public void clear() {
		mMap.clear();
	}

	@Override
	public Set<K> keySet() {
		return mMap.keySet();
	}

	@Override
	public Collection<V> values() {
		return mMap.values();
	}

	@Override
	public Set<Entry<K, V>> entrySet() {
		return mMap.entrySet();
	}

	/**
	 * Constructs values for a {@link Construction Cache}
	 */
	@FunctionalInterface
	public interface IValueConstruction<K, V> {
		V constructValue(K key);
	}

}
