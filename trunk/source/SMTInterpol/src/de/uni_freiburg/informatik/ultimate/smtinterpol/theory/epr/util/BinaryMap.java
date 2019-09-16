package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A very simple map for storing exactly two mappings. Similar to {@see java.util.Collections#singletonMap}.
 *
 * @author hoenicke
 *
 * @param <K>
 *            The key type.
 * @param <V>
 *            The value type.
 */
public class BinaryMap<K, V> extends AbstractMap<K, V> {
	private final K mKey1, mKey2;
	private V mValue1, mValue2;

	public BinaryMap(final K key1, final V value1, final K key2, final V value2) {
		mKey1 = key1;
		mValue1 = value1;
		mKey2 = key2;
		mValue2 = value2;
	}

	private class Entry implements Map.Entry<K, V> {
		private final int mId;

		public Entry(final int id) {
			mId = id;
		}

		@Override
		public K getKey() {
			return mId == 0 ? mKey1 : mKey2;
		}

		@Override
		public V getValue() {
			return mId == 0 ? mValue1 : mValue2;
		}

		@Override
		public V setValue(final V value) {
			final V old;
			if (mId == 0) {
				old = mValue1;
				mValue1 = value;
			} else {
				old = mValue2;
				mValue2 = value;
			}
			return old;
		}

		@Override
		public String toString() {
			return getKey() + " -> " + getValue();
		}
	}

	@Override
	public Set<Map.Entry<K, V>> entrySet() {
		return new AbstractSet<Map.Entry<K, V>>() {

			@Override
			public Iterator<Map.Entry<K, V>> iterator() {
				return new Iterator<Map.Entry<K, V>>() {
					private int mId = 0;

					@Override
					public boolean hasNext() {
						return mId < 2;
					}

					@Override
					public Map.Entry<K, V> next() {
						if (mId < 2) {
							return new Entry(mId++);
						}
						throw new NoSuchElementException();
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException("No remove!");
					}

				};
			}

			@Override
			public int size() {
				return 2;
			}
		};
	}
}
