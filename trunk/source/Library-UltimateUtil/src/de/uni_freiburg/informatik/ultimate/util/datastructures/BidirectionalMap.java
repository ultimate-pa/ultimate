/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A bidirectional map is a 1:1 mapping, having unique keys and unique values.
 * Every bidirectional map can be inverted to receive a map from values to keys.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <K> type of keys inside this map / type of values inside this map's inverse
 * @param <V> type of values inside this map / type of keys inside this map's inverse
 */
public class BidirectionalMap<K, V> extends HashMap<K, V> {

	private static final long serialVersionUID = -7727684030243112324L;

	private final BidirectionalMap<V, K> mInverse;

	public BidirectionalMap() {
		super();
		mInverse = new BidirectionalMap<>(new HashMap<>(), this);
	}

	/**
	 * Creates a copy of a given bidirectional map.
	 * 
	 * @param biMap map to be copied
	 */
	public BidirectionalMap(BidirectionalMap<K, V> biMap) {
		super(biMap);
		mInverse = new BidirectionalMap<>(biMap.mInverse, this);
	}

	private BidirectionalMap(HashMap<K, V> map, BidirectionalMap<V, K> inverse) {
		super(map);
		mInverse = inverse;
	}

	/**
	 * Returns the inverse of this map. 
	 * The inverse is a map where this map's values are mapped to this map's keys.
	 * 
	 * @return inverse of this map
	 */
	public BidirectionalMap<V, K> inverse() {
		return mInverse;
	}
	
	@Override
	public void clear() {
		clearAsymmetric();
		mInverse.clearAsymmetric();
	}
	
	private void clearAsymmetric() {
		super.clear();
	}

	@Override
	public boolean containsValue(Object value) {
		// better performance: O(1) instead of O(n)
		return mInverse.containsKey(value);
	}

	/**
	 * Adds the specified mapping to this map.
	 * Every existing mapping of the form {@code (key, *)} or {@code (*, value)} will be replaced.
	 * 
	 * @param key     key to be associated with the specified value
	 * @param value   value to be associated with the specified key
	 */
	@Override
	public V put(K key, V value) {
		final K oldKey = mInverse.putAsymmetric(value, key);
		removeAsymmetric(oldKey);
		final V oldValue = putAsymmetric(key, value);
		mInverse.removeAsymmetric(oldValue);
		return oldValue;
	}

	public V putAsymmetric(K key, V value) {
		return super.put(key, value);
	}

	@Override
	public V remove(Object key) {
		final V removedValue = removeAsymmetric(key);
		mInverse.removeAsymmetric(removedValue);
		return removedValue;
	}

	public V removeAsymmetric(Object key) {
		return super.remove(key);
	}

	/**
	 * Returns a read-only {@link Set} view of this map's keys.
	 * This map's key set is equal to the value set of this map's inverse.
	 * 
	 * @return read-only {@link Set} view of this map's keys
	 */
	@Override
	public Set<K> keySet() {
		return Collections.unmodifiableSet(super.keySet());
	}
	
	/**
	 * Returns a read-only {@link Set} view of this map's values.
	 * This map's value set is equal to the key set of this map's inverse.
	 * <p>
	 * Note that general maps return only a {@link Collection} since they do not ensure uniqueness of their values. 
	 * 
	 * @return read-only {@link Set} view of this map's values
	 */
	@Override
	public Set<V> values() {
		return mInverse.keySet();
	}

	/**
	 * Returns a read-only {@link Set} view of this map's mappings.
	 * <p>
	 * <b>Do not use {@link Map.Entry#setValue(Object)}!</b>
	 * {@code setValue} changes only one side of this BidirectionalMap.
	 * Changing values using {@code setValue} breaks this map.
	 * 
	 * @return read-only {@link Set} view of this map's mappings
	 */
	@Override
	public Set<Map.Entry<K, V>> entrySet() {
		return Collections.unmodifiableSet(super.entrySet());
	}

	/**
	 * Copies all mappings from the specified map to this map.
	 * Existing mappings from this map with keys or values occurring in the the specified map will be overwritten.
	 * <p>
	 * <b>The outcome may depend on the iteration order of the specified map</b>
	 * unless all of the following propositions hold:
	 * <ul>
	 *   <li>{@code this.keySet()} &cap; {@code m.keySet()} = &empty;</li>
	 *   <li>{@code this.values()} &cap; {@code m.values()} = &empty;</li>
	 *   <li>All values in {@code m.values()} are unique</li>
	 * </ul>
	 * 
	 * @param m mappings to be stored in this map
	 */
	@Override
	public void putAll(Map<? extends K,? extends V> m) {
		for (final Map.Entry<? extends K,? extends V> e : m.entrySet()) {
			put(e.getKey(), e.getValue());
		}
	}

	// equals() and hashCode() from super class work for this implementation
}
