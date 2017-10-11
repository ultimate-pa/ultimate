/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;

/**
 * TODO: comment
 * @author Matthias Heizmann
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <K1>
 * @param <K2>
 * @param <K3>
 * @param <V>
 */
public class NestedMap4<K1, K2, K3, K4, V> {
	
	private final Map<K1, NestedMap3<K2, K3, K4, V>> mK1ToK2ToK3ToK4V = 
			new HashMap<K1, NestedMap3<K2, K3, K4, V>>();
	
	/**
	 * Returns a stream to all values of the nested map.
	 * 
	 * @return A stream to all values of the nested map
	 */
	public Stream<V> values() {
		return this.mK1ToK2ToK3ToK4V.values().stream().flatMap(NestedMap3::values);
	}
	
	public V put(final K1 key1, final K2 key2, final K3 key3, final K4 key4, final V value) {
		NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(key1);
		if (k2tok3tok4toV == null) {
			k2tok3tok4toV = new NestedMap3<>();
			mK1ToK2ToK3ToK4V.put(key1, k2tok3tok4toV);
		}
		return k2tok3tok4toV.put(key2, key3, key4, value);
	}
	
	public V get(final K1 key1, final K2 key2, final K3 key3, final K4 key4) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(key1);
		if (k2tok3tok4toV == null) {
			return null;
		} else {
			return k2tok3tok4toV.get(key2, key3, key4);
		}
	}
	
	public Map<K4, V> get(final K1 key1, final K2 key2, final K3 key3) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(key1);
		if (k2tok3tok4toV == null) {
			return null;
		} else {
			return k2tok3tok4toV.get(key2, key3);
		}
	}
	
	public NestedMap2<K3, K4, V> get(final K1 key1, final K2 key2) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(key1);
		if (k2tok3tok4toV == null) {
			return null;
		} else {
			return k2tok3tok4toV.get(key2);
		}
	}
	
	public NestedMap3<K2, K3, K4, V> get(final K1 key1) {
		return mK1ToK2ToK3ToK4V.get(key1);
	}
	
	public void clear() {
		mK1ToK2ToK3ToK4V.clear();
	}
	
	public Set<K1> keySet() {
		return mK1ToK2ToK3ToK4V.keySet();
	}
	
	
	public Iterable<Quin<K1, K2, K3, K4, V>> entrySet() {
		final Iterator<Entry<K1, NestedMap3<K2, K3, K4, V>>> innerIterator = mK1ToK2ToK3ToK4V.entrySet().iterator();
		final Function<Entry<K1, NestedMap3<K2, K3, K4, V>>, Iterator<Quad<K2, K3, K4, V>>> nextOuterIteratorProvider = (x -> x
				.getValue().entrySet().iterator());
		final Function<Entry<K1, NestedMap3<K2, K3, K4, V>>, Function<Quad<K2, K3, K4, V>, Quin<K1, K2, K3, K4, V>>> resultProvider = (x -> (y -> new Quin<K1, K2, K3, K4, V>(
				x.getKey(), y.getFirst(), y.getSecond(), y.getThird(), y.getFourth())));
		return () -> new NestedIterator<Entry<K1, NestedMap3<K2, K3, K4, V>>, Quad<K2, K3, K4, V>, Quin<K1, K2, K3, K4, V>>(
				innerIterator, nextOuterIteratorProvider, resultProvider);
	}
	
	/**
	 * @return all entries where first element is k1
	 */
	public Iterable<Quin<K1, K2, K3, K4, V>> entries(final K1 k1) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = get(k1);
		if (k2tok3tok4toV == null) {
			return Collections.emptySet();
		} else {
			final Function<Quad<K2, K3, K4, V>, Quin<K1, K2, K3, K4, V>> transformer = (x -> new Quin<K1, K2, K3, K4, V>(k1, x.getFirst(), x.getSecond(),
					x.getThird(), x.getFourth()));
			return () -> new TransformIterator<Quad<K2, K3, K4, V>, Quin<K1, K2, K3, K4, V>>(k2tok3tok4toV.entrySet().iterator(),
					transformer);
		}
	}
	
	/**
	 * @return all entries where first element is k1 and the second element is k2
	 */
	public Iterable<Quin<K1, K2, K3, K4, V>> entries(final K1 k1, final K2 k2) {
		final NestedMap2<K3, K4, V> k3tok4toV = get(k1, k2);
		if (k3tok4toV == null) {
			return Collections.emptySet();
		} else {
			final Function<Triple<K3, K4, V>, Quin<K1, K2, K3, K4, V>> transformer = (x -> new Quin<K1, K2, K3, K4, V>(
					k1, k2, x.getFirst(), x.getSecond(), x.getThird()));
			return () -> new TransformIterator<Triple<K3, K4, V>, Quin<K1, K2, K3, K4, V>>(
					k3tok4toV.entrySet().iterator(), transformer);
		}
	}

	
	
	
	public NestedMap3<K2, K3, K4, V> remove(final K1 k1) {
		return mK1ToK2ToK3ToK4V.remove(k1);
	}

	public NestedMap2<K3, K4, V> remove(final K1 k1, final K2 k2) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(k1);
		if (k2tok3tok4toV == null) {
			return null;
		}
		return k2tok3tok4toV.remove(k2);
	}
	
	public Map<K4, V> remove(final K1 k1, final K2 k2, final K3 k3) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(k1);
		if (k2tok3tok4toV == null) {
			return null;
		}
		return k2tok3tok4toV.remove(k2, k3);
	}
	
	public V remove(final K1 k1, final K2 k2, final K3 k3, final K4 k4) {
		final NestedMap3<K2, K3, K4, V> k2tok3tok4toV = mK1ToK2ToK3ToK4V.get(k1);
		if (k2tok3tok4toV == null) {
			return null;
		}
		return k2tok3tok4toV.remove(k2, k3, k4);
	}
	
	public int size() {
		int result = 0;
		for (final Entry<K1, NestedMap3<K2, K3, K4, V>> entry : mK1ToK2ToK3ToK4V.entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}
}
