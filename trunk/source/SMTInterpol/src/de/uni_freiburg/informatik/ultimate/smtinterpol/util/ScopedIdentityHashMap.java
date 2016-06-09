/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.ScopeUtils;

/**
 * A scoped map implementation based on identity maps.  This map violates the
 * map contract in the same way as IdentityHashMap does.
 * 
 * Null values are not permitted.
 * @author Juergen Christ
 */
public class ScopedIdentityHashMap<K, V> extends AbstractMap<K, V> {

	IdentityHashMap<K, V> mMap;
	IdentityHashMap<K, V>[] mHistory;
	int mCurScope = -1;

	@SuppressWarnings("unchecked")
	public ScopedIdentityHashMap() {
		mMap = new IdentityHashMap<K, V>();
		mHistory = new IdentityHashMap[ScopeUtils.NUM_INITIAL_SCOPES];
	}

	private IdentityHashMap<K, V> undoMap() {
		return mHistory[mCurScope];
	}

	private void recordUndo(K key, V value) {
		if (mCurScope != -1) {
			final Map<K, V> old = undoMap();
			if (!old.containsKey(key)) {
				old.put(key, value);
			}
		}
	}

	private void undoEntry(Entry<K,V> old) {
		if (old.getValue() == null) {
			mMap.remove(old.getKey());
		} else {
			mMap.put(old.getKey(), old.getValue());
		}
	}

	public void beginScope() {
		if (mCurScope == mHistory.length - 1) {
			mHistory = ScopeUtils.grow(mHistory);
		}
		mHistory[++mCurScope] = new IdentityHashMap<K, V>();
	}

	public void endScope() {
		for (final Entry<K, V> old : undoMap().entrySet()) {
			undoEntry(old);
		}
		mHistory[mCurScope--] = null;
		if (ScopeUtils.shouldShrink(mHistory)) {
			mHistory = ScopeUtils.shrink(mHistory);
		}
	}

	public Iterable<Map.Entry<K, V>> currentScopeEntries() {
		if (mCurScope == -1) {
			return entrySet();
		}
		return new AbstractSet<Map.Entry<K, V>>() {
			@Override
			public Iterator<Map.Entry<K, V>> iterator() {
				return new Iterator<Map.Entry<K, V>>() {
					Iterator<Entry<K, V>> mBacking =
							undoMap().entrySet().iterator();
					Entry<K, V> mLast;

					@Override
					public boolean hasNext() {
						return mBacking.hasNext();
					}

					@Override
					public Map.Entry<K, V> next() {
						final K key = (mLast = mBacking.next()).getKey();
						return new Entry<K, V>() {
							@Override
							public K getKey() {
								return key;
							}

							@Override
							public V getValue() {
								return mMap.get(key);
							}

							@Override
							public V setValue(V value) {
								return mMap.put(key, value);
							}
						};
					}

					@Override
					public void remove() {
						mBacking.remove();
						undoEntry(mLast);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	public Iterable<K> currentScopeKeys() {
		if (mCurScope == -1) {
			return keySet();
		}
		return new AbstractSet<K>() {
			@Override
			public Iterator<K> iterator() {
				return new Iterator<K>() {

					Iterator<Entry<K, V>> mBacking =
							undoMap().entrySet().iterator();
					Entry<K, V> mLast;

					@Override
					public boolean hasNext() {
						return mBacking.hasNext();
					}

					@Override
					public K next() {
						return (mLast = mBacking.next()).getKey();
					}

					@Override
					public void remove() {
						mBacking.remove();
						undoEntry(mLast);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	public Iterable<V> currentScopeValues() {
		if (mCurScope == -1) {
			return values();
		}
		return new AbstractSet<V>() {
			@Override
			public Iterator<V> iterator() {
				return new Iterator<V>() {

					Iterator<Entry<K, V>> mBacking =
							undoMap().entrySet().iterator();
					Entry<K, V> mLast;

					@Override
					public boolean hasNext() {
						return mBacking.hasNext();
					}

					@Override
					public V next() {
						return mMap.get((mLast = mBacking.next()).getKey());
					}

					@Override
					public void remove() {
						mBacking.remove();
						undoEntry(mLast);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	@SuppressWarnings("unchecked")
	@Override
	public void clear() {
		mMap.clear();
		mHistory = new IdentityHashMap[ScopeUtils.NUM_INITIAL_SCOPES];
	}

	@Override
	public boolean containsKey(Object key) {
		return mMap.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return mMap.containsValue(value);
	}

	@Override
	public V get(Object key) {
		return mMap.get(key);
	}

	@Override
	public boolean isEmpty() {
		return mMap.isEmpty();
	}

	public boolean isEmptyScope() {
		return mCurScope == -1;
	}

	@Override
	public Set<Entry<K,V>> entrySet() {
		return new AbstractSet<Entry<K,V>>() {

			@Override
			public Iterator<Entry<K,V>> iterator() {
				return new Iterator<Entry<K,V>>() {

					Iterator<Entry<K,V>> mBacking = mMap.entrySet().iterator();
					Entry<K,V> mLast;

					@Override
					public boolean hasNext() {
						return mBacking.hasNext();
					}

					@Override
					public Entry<K,V> next() {
						return mLast = mBacking.next();
					}

					@Override
					public void remove() {
						mBacking.remove();
						recordUndo(mLast.getKey(), mLast.getValue());
					}
				};
			}

			@Override
			public int size() {
				return mMap.size();
			}
		};
	}

	@Override
	public V put(K key, V value) {
		if (value == null) {
			throw new NullPointerException();
		}
		final V oldval = mMap.put(key, value);
		recordUndo(key, oldval);
		return oldval;
	}

	@SuppressWarnings("unchecked")
	@Override
	public V remove(Object key) {
		final V oldval = mMap.remove(key);
		recordUndo((K) key, oldval);
		return oldval;
	}

	@Override
	public int size() {
		return mMap.size();
	}

	public int currentScopeSize() {
		return undoMap().size();
	}

	public int getActiveScopeNum() {
		return mCurScope + 1;
	}
}
