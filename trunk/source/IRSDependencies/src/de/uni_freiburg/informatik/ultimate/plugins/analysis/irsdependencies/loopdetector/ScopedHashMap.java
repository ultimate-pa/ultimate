package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class ScopedHashMap<K, V> implements Map<K, V> {

	private Deque<Map<K, V>> mScopes;

	public ScopedHashMap() {
		clear();
	}

	public ScopedHashMap(ScopedHashMap<K, V> otherMap) {
		mScopes = new ArrayDeque<Map<K, V>>();
		for (Map<K, V> map : otherMap.mScopes) {
			mScopes.addLast(new HashMap<>(map));
		}
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isEmpty() {
		for (Map<K, V> map : mScopes) {
			if (!map.isEmpty()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean containsKey(Object key) {
		for (Map<K, V> map : mScopes) {
			if (map.containsKey(key)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean containsValue(Object value) {
		for (Map<K, V> map : mScopes) {
			if (map.containsValue(value)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public V get(Object key) {
		for (Map<K, V> map : mScopes) {
			final V val = map.get(key);
			if (val != null) {
				return val;
			}
		}
		return null;
	}

	@Override
	public V put(K key, V value) {
		return mScopes.peekFirst().put(key, value);
	}

	@Override
	public V remove(Object key) {
		return mScopes.peekFirst().remove(key);
	}

	@Override
	public void putAll(Map<? extends K, ? extends V> m) {
		mScopes.peekFirst().putAll(m);
	}

	@Override
	public void clear() {
		mScopes = new ArrayDeque<Map<K, V>>();
		mScopes.addFirst(new HashMap<K, V>());
	}

	@Override
	public Set<K> keySet() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<V> values() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<java.util.Map.Entry<K, V>> entrySet() {
		throw new UnsupportedOperationException();
	}

	public void beginScope() {
		mScopes.addFirst(new HashMap<K, V>());
	}

	public void endScope() {
		mScopes.removeFirst();
	}

	public int getScopesCount() {
		return mScopes.size() - 1;
	}

	@Override
	public String toString() {
		return mScopes.toString();
	}

}
