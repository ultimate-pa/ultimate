/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;

/**
 * TODO: comment
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <K1>
 * @param <K2>
 * @param <K3>
 * @param <V>
 */
public class NestedMap3<K1, K2, K3, V> {

	private final Map<K1, NestedMap2<K2, K3, V>> mK1ToK2ToK3V =
			new HashMap<>();

	/**
	 * Construct an empty NestedMap3
	 */
	public NestedMap3() {
	}
	
	/**
	 * Returns a stream to all values of the nested map.
	 * 
	 * @return A stream to all values of the nested map
	 */
	public Stream<V> values() {
		return this.mK1ToK2ToK3V.values().stream().flatMap(NestedMap2::values);
	}

	/**
	 * Copy constructor
	 *
	 * @param original
	 */
	public NestedMap3(final NestedMap3<K1, K2, K3, V> original) {
		for (final K1 k1 : original.keySet()) {
			mK1ToK2ToK3V.put(k1, new NestedMap2<>(original.get(k1)));
		}
	}

	public V put(final K1 key1, final K2 key2, final K3 key3, final V value) {
		NestedMap2<K2, K3, V> k2tok3toV = mK1ToK2ToK3V.get(key1);
		if (k2tok3toV == null) {
			k2tok3toV = new NestedMap2<>();
			mK1ToK2ToK3V.put(key1, k2tok3toV);
		}
		return k2tok3toV.put(key2, key3, value);
	}

	public V get(final K1 key1, final K2 key2, final K3 key3) {
		final NestedMap2<K2, K3, V> k2tok3toV = mK1ToK2ToK3V.get(key1);
		if (k2tok3toV == null) {
			return null;
		} else {
			return k2tok3toV.get(key2, key3);
		}
	}

	public Map<K3, V> get(final K1 key1, final K2 key2) {
		final NestedMap2<K2, K3, V> k2toV = mK1ToK2ToK3V.get(key1);
		if (k2toV == null) {
			return null;
		} else {
			return k2toV.get(key2);
		}
	}

	public NestedMap2<K2, K3, V> get(final K1 key1) {
		return mK1ToK2ToK3V.get(key1);
	}

	public Set<K1> keySet() {
		return mK1ToK2ToK3V.keySet();
	}

	public void clear() {
		mK1ToK2ToK3V.clear();
	}

	public Iterable<Triple<K1, K2, K3>> keys3() {
		final Iterator<Entry<K1, NestedMap2<K2, K3, V>>> innerIterator = mK1ToK2ToK3V.entrySet().iterator();
		final Function<Entry<K1, NestedMap2<K2, K3, V>>, Iterator<Pair<K2, K3>>> nextOuterIteratorProvider = (x -> x
				.getValue().keys2().iterator());
		final Function<Entry<K1, NestedMap2<K2, K3, V>>, Function<Pair<K2, K3>, Triple<K1, K2, K3>>> resultProvider = (x -> (y -> new Triple<K1, K2, K3>(
				x.getKey(), y.getFirst(), y.getSecond())));
		return () -> new NestedIterator<Entry<K1, NestedMap2<K2, K3, V>>, Pair<K2, K3>, Triple<K1, K2, K3>>(
				innerIterator, nextOuterIteratorProvider, resultProvider);
	}

	public Iterable<Quad<K1, K2, K3, V>> entrySet() {
		final Iterator<Entry<K1, NestedMap2<K2, K3, V>>> innerIterator = mK1ToK2ToK3V.entrySet().iterator();
		final Function<Entry<K1, NestedMap2<K2, K3, V>>, Iterator<Triple<K2, K3, V>>> nextOuterIteratorProvider = (x -> x
				.getValue().entrySet().iterator());
		final Function<Entry<K1, NestedMap2<K2, K3, V>>, Function<Triple<K2, K3, V>, Quad<K1, K2, K3, V>>> resultProvider = (x -> (y -> new Quad<K1, K2, K3, V>(
				x.getKey(), y.getFirst(), y.getSecond(), y.getThird())));
		return () -> new NestedIterator<Entry<K1, NestedMap2<K2, K3, V>>, Triple<K2, K3, V>, Quad<K1, K2, K3, V>>(
				innerIterator, nextOuterIteratorProvider, resultProvider);
	}

	/**
	 * @return all entries where first element is k1
	 */
	public Iterable<Quad<K1, K2, K3, V>> entries(final K1 k1) {
		final NestedMap2<K2, K3, V> k2Tok3ToV = get(k1);
		if (k2Tok3ToV == null) {
			return Collections.emptySet();
		} else {
			final Function<Triple<K2, K3, V>, Quad<K1, K2, K3, V>> transformer = (x -> new Quad<K1, K2, K3, V>(k1, x.getFirst(), x.getSecond(),
					x.getThird()));
			return () -> new TransformIterator<Triple<K2, K3, V>, Quad<K1, K2, K3, V>>(k2Tok3ToV.entrySet().iterator(),
					transformer);
		}
	}

	/**
	 * @return all entries where first element is k1 and the second element is k2
	 */
	public Iterable<Quad<K1, K2, K3, V>> entries(final K1 k1, final K2 k2) {
		final Map<K3, V> k3ToV = get(k1, k2);
		if (k3ToV == null) {
			return Collections.emptySet();
		} else {
			final Function<Entry<K3, V>, Quad<K1, K2, K3, V>> transformer = (x -> new Quad<K1, K2, K3, V>(k1, k2, x.getKey(),
					x.getValue()));
			return () -> new TransformIterator<Entry<K3, V>, Quad<K1, K2, K3, V>>(k3ToV.entrySet().iterator(),
					transformer);
		}
	}

	public  NestedMap2<K2, K3, V> remove(final K1 k1) {
		return mK1ToK2ToK3V.remove(k1);
	}

	public Map<K3, V> remove(final K1 k1, final K2 k2) {
		final NestedMap2<K2, K3, V> k1Tok2ToV = mK1ToK2ToK3V.get(k1);
		if (k1Tok2ToV == null) {
			return null;
		}
		return k1Tok2ToV.remove(k2);
	}

	public V remove(final K1 k1, final K2 k2, final K3 k3) {
		final NestedMap2<K2, K3, V> k1Tok2ToV = mK1ToK2ToK3V.get(k1);
		if (k1Tok2ToV == null) {
			return null;
		}
		return k1Tok2ToV.remove(k2, k3);
	}


	public int size() {
		int result = 0;
		for (final Entry<K1, NestedMap2<K2, K3, V>> entry : mK1ToK2ToK3V.entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

//	/**
//	 * Makes a deep copy of this NestedMap3.
//	 * (but not the objects it holds)
//	 * (added by Alexander Nutz)
//	 * @deprecated replace by constructor
//	 */
//	@Deprecated
//	public NestedMap3<K1, K2, K3, V> copy() {
//		final NestedMap3<K1, K2, K3, V> result = new NestedMap3<>();
//		for (final K1 k1 : this.keySet()) {
//			result.mK1ToK2ToK3V.put(k1, this.get(k1).copy());
//		}
//		return result;
//	}

	public Set<K2> projektTo2() {
		final Set<K2> result = new HashSet<>();
		for (final Entry<K1, NestedMap2<K2, K3, V>> entry : mK1ToK2ToK3V.entrySet()) {
			result.addAll(entry.getValue().keySet());
		}
		return result;
	}
}
