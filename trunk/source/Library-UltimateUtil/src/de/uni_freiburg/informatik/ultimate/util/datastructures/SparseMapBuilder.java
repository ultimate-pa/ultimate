/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Auxiliary class for building Maps. Objects of this class return
 * <ul>
 * <li>a {@link Collections#emptyMap} if the built map contains no elements,
 * <li>a {@link Collections#singletonMap} if the built map contains exactly one
 * element, and
 * <li>a {@link HashMap} if the built map contains two or more elements.
 * </ul>
 * This class deliberately does not implement the Map interface. Such an
 * extension of this class would be possible but such an extension would be
 * very complex since methods like {@link Map#entrySet()} return a view on
 * the underlying Map and can modify the unterlying Map.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SparseMapBuilder<K, V> {
	private static final String MAP_CANNOT_BE_MODIFIED_AFTER_THE_RESULT_WAS_RETURNED = "Map cannot be modified after the result was returned.";
	private boolean mConstructionFinished;
	private Map<K, V> mMap;

	public V put(final K key, final V value) {
		if (mConstructionFinished) {
			throw new IllegalStateException(MAP_CANNOT_BE_MODIFIED_AFTER_THE_RESULT_WAS_RETURNED);
		}
		if (mMap.isEmpty()) {
			mMap = Collections.singletonMap(key, value);
			// there was no old value
			return null;
		} else {
			if (mMap.size() == 1) {
				final HashMap<K, V> newMap = new HashMap<>();
				newMap.putAll(mMap);
				mMap = newMap;
			}
			return mMap.put(key, value);
		}
	}

	/**
	 * Returns the Map the was built. Afterwards the {@link SparseMapBuilder} cannot
	 * modify this map any more.
	 */
	public Map<K, V> getBuiltMap() {
		mConstructionFinished = true;
		return mMap;
	}

	public void clear() {
		if (mConstructionFinished) {
			throw new IllegalStateException(MAP_CANNOT_BE_MODIFIED_AFTER_THE_RESULT_WAS_RETURNED);
		}
		mMap = Collections.emptyMap();
	}

	public boolean containsKey(final Object key) {
		return mMap.containsKey(key);
	}

	public boolean containsValue(final Object value) {
		return mMap.containsValue(value);
	}

	public V get(final Object key) {
		return mMap.get(key);
	}

	public boolean isEmpty() {
		return mMap.isEmpty();
	}

	public V remove(final Object key) {
		if (mConstructionFinished) {
			throw new IllegalStateException(MAP_CANNOT_BE_MODIFIED_AFTER_THE_RESULT_WAS_RETURNED);
		}
		final V result;
		if (mMap.containsKey(key)) {
			if (mMap.size() == 2) {
				result = mMap.remove(key);
				final Entry<K, V> remainingEntry = mMap.entrySet().iterator().next();
				mMap = Collections.singletonMap(remainingEntry.getKey(), remainingEntry.getValue());
			} else if (mMap.size() == 1) {
				result = mMap.remove(key);
				mMap = Collections.emptyMap();
			} else {
				result = mMap.remove(key);
			}
		} else {
			result = null;
		}
		return result;
	}

	public int size() {
		return mMap.size();
	}



}
