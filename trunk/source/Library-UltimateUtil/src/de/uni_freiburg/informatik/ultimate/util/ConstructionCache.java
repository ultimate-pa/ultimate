/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Allows to construct objects lazily.
 * Stores a Map from keys to values. The getOrConstruct methods will return 
 * the value for a given key if the value was already constructed. I the
 * the value was not already constructed it is constructed at the first call
 * of the getOrConstruct method.
 * Construction of elements is done by Objects that implement this 
 * IValueConstruction interface of this class.
 * @author Matthias Heizmann
 *
 * @param <K>
 * @param <V>
 */
public class ConstructionCache<K, V> {
	private final Map<K,V> mMap = new HashMap<>();
	private final IValueConstruction<K, V> mValueComputation;
	
	
	/**
	 * Constructs values for a {@link Construction Cache}
	 *
	 * @param <K>
	 * @param <V>
	 */
	public interface IValueConstruction<K, V> {
		public V constructValue(K key);
	}
	
	public ConstructionCache(IValueConstruction<K, V> valueConstruction) {
		mValueComputation = valueConstruction;
	}
	
	/**
	 * Get value stored for key. Construct value if not already constructed.
	 */
	public V getOrConstruct(K key) {
		V value = mMap.get(key);
		if (value == null) {
			value = mValueComputation.constructValue(key);
			mMap.put(key, value);
		}
		return value;
	}
	
	public Map<K, V> getMap() {
		return Collections.unmodifiableMap(mMap);
	}
	

}
