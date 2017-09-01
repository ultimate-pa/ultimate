/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;

/**
 * TODO: comment
 *
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <K1>
 * @param <K2>
 * @param <V>
 */
public class NestedMap2<K1, K2, V> {

	private final Map<K1, Map<K2, V>> mK1ToK2ToV = new HashMap<>();

	/**
	 * Construct an empty NestedMap2
	 */
	public NestedMap2() {
	}

	/**
	 * Copy constructor
	 */
	public NestedMap2(final NestedMap2<K1, K2, V> original) {
		for (final K1 k1 : original.keySet()) {
			mK1ToK2ToV.put(k1, new HashMap<>(original.get(k1)));
		}
	}

	public V put(final K1 key1, final K2 key2, final V value) {
		Map<K2, V> k2toV = mK1ToK2ToV.get(key1);
		if (k2toV == null) {
			k2toV = new HashMap<>();
			mK1ToK2ToV.put(key1, k2toV);
		}
		return k2toV.put(key2, value);
	}

	public V get(final K1 key1, final K2 key2) {
		final Map<K2, V> k2toV = mK1ToK2ToV.get(key1);
		if (k2toV == null) {
			return null;
		}
		return k2toV.get(key2);
	}

	public Map<K2, V> get(final K1 key1) {
		return mK1ToK2ToV.get(key1);
	}

	public Set<K1> keySet() {
		return mK1ToK2ToV.keySet();
	}

	public Iterable<Pair<K1, K2>> keys2() {
		return () -> new Iterator<Pair<K1, K2>>() {
			private Iterator<Entry<K1, Map<K2, V>>> mIterator1;
			private Entry<K1, Map<K2, V>> mIterator1Object;
			private Iterator<K2> mIterator2;

			{
				mIterator1 = mK1ToK2ToV.entrySet().iterator();
				if (mIterator1.hasNext()) {
					mIterator1Object = mIterator1.next();
					mIterator2 = mIterator1Object.getValue().keySet().iterator();
				}
			}

			@Override
			public boolean hasNext() {
				if (mIterator1Object == null) {
					return false;
				}
				return mIterator2.hasNext();
			}

			@Override
			public Pair<K1, K2> next() {
				if (mIterator1Object == null) {
					throw new NoSuchElementException();
				}
				if (!mIterator2.hasNext()) {
					if (!mIterator1.hasNext()) {
						throw new NoSuchElementException();
					}
					mIterator1Object = mIterator1.next();
					assert mIterator1Object.getValue().size() > 0 : "must contain at least one value";
					mIterator2 = mIterator1Object.getValue().keySet().iterator();
				}
				return new Pair<>(mIterator1Object.getKey(), mIterator2.next());
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("not yet implemented");
			}
		};

	}

	public Iterable<Triple<K1, K2, V>> entrySet() {
		final Iterator<Entry<K1, Map<K2, V>>> innerIterator = mK1ToK2ToV.entrySet().iterator();
		final Function<Entry<K1, Map<K2, V>>, Iterator<Entry<K2, V>>> nextOuterIteratorProvider = (x -> x.getValue()
				.entrySet().iterator());
		final Function<Entry<K1, Map<K2, V>>, Function<Entry<K2, V>, Triple<K1, K2, V>>> resultProvider = (x -> (y -> new Triple<K1, K2, V>(
				x.getKey(), y.getKey(), y.getValue())));
		return () -> new NestedIterator<Entry<K1, Map<K2, V>>, Entry<K2, V>, Triple<K1, K2, V>>(innerIterator,
				nextOuterIteratorProvider, resultProvider);
	}

	/**
	 * @return all entries where first element is k1
	 */
	public Iterable<Triple<K1, K2, V>> entries(final K1 k1) {
		final Map<K2, V> k2ToV = mK1ToK2ToV.get(k1);
		if (k2ToV == null) {
			return Collections.emptySet();
		} else {
			final Function<Entry<K2, V>, Triple<K1, K2, V>> transformer = (x -> new Triple<K1, K2, V>(k1, x.getKey(),
					x.getValue()));
			return () -> new TransformIterator<Entry<K2, V>, Triple<K1, K2, V>>(k2ToV.entrySet().iterator(),
					transformer);
		}
	}

	public void addAll(final NestedMap2<K1, K2, V> nestedMap) {
		for (final Triple<K1, K2, V> triple : nestedMap.entrySet()) {
			this.put(triple.getFirst(), triple.getSecond(), triple.getThird());
		}
	}

	public Map<K2, V> remove(final K1 k1) {
		return mK1ToK2ToV.remove(k1);
	}

	public V remove(final K1 k1, final K2 k2) {
		final Map<K2, V> k2ToV = mK1ToK2ToV.get(k1);
		if (k2ToV == null) {
			return null;
		}
		return k2ToV.remove(k2);
	}

	/**
	 * Removes all triples from the given map whose second entry equals the given argument.
	 *
	 * @param k2
	 */
	public void removeK2(final K2 k2) {
		for (final K1 k1 : mK1ToK2ToV.keySet()) {
			mK1ToK2ToV.get(k1).remove(k2);
		}
	}

	public void replaceK2(final K2 k2orig, final K2 k2new, final boolean allowThatNewK2isAlreadyPresent) {
		if (allowThatNewK2isAlreadyPresent) {
			throw new UnsupportedOperationException("implement this?");
		}
		for (final K1 k1 : mK1ToK2ToV.keySet()) {
			final Map<K2, V> innerMap = mK1ToK2ToV.get(k1);
			final V k2Contents = innerMap.get(k2orig);
			if (k2Contents == null) {
				continue;
			}
			if (innerMap.containsKey(k2new)) {
				throw new IllegalStateException();
			}
			innerMap.put(k2new, k2Contents);
			innerMap.remove(k2orig);
		}
	}

	@Override
	public String toString() {
		return mK1ToK2ToV.toString();
	}

	public void clear() {
		mK1ToK2ToV.clear();
	}

	public int size() {
		int result = 0;
		for (final Entry<K1, Map<K2, V>> entry : mK1ToK2ToV.entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mK1ToK2ToV == null ? 0 : mK1ToK2ToV.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final NestedMap2 other = (NestedMap2) obj;
		if (mK1ToK2ToV == null) {
			if (other.mK1ToK2ToV != null) {
				return false;
			}
		} else if (!mK1ToK2ToV.equals(other.mK1ToK2ToV)) {
			return false;
		}
		return true;
	}

	public boolean isEmpty() {
		return mK1ToK2ToV.isEmpty();
	}
}
