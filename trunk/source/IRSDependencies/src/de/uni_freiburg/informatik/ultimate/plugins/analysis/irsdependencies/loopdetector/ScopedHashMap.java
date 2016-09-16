/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
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
		assert !mScopes.isEmpty();
	}

	public ScopedHashMap(final ScopedHashMap<K, V> otherMap) {
		mScopes = new ArrayDeque<>();
		for (final Map<K, V> map : otherMap.mScopes) {
			mScopes.addLast(new HashMap<>(map));
		}
		assert !mScopes.isEmpty();
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isEmpty() {
		for (final Map<K, V> map : mScopes) {
			if (!map.isEmpty()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean containsKey(final Object key) {
		for (final Map<K, V> map : mScopes) {
			if (map.containsKey(key)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean containsValue(final Object value) {
		for (final Map<K, V> map : mScopes) {
			if (map.containsValue(value)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public V get(final Object key) {
		for (final Map<K, V> map : mScopes) {
			final V val = map.get(key);
			if (val != null) {
				return val;
			}
		}
		return null;
	}

	@Override
	public V put(final K key, final V value) {
		return mScopes.peekFirst().put(key, value);
	}

	@Override
	public V remove(final Object key) {
		return mScopes.peekFirst().remove(key);
	}

	@Override
	public void putAll(final Map<? extends K, ? extends V> m) {
		mScopes.peekFirst().putAll(m);
	}

	@Override
	public void clear() {
		mScopes = new ArrayDeque<>();
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
		assert !mScopes.isEmpty() : "You ended a scope you did not begin";
	}

	public int getScopesCount() {
		return mScopes.size() - 1;
	}

	@Override
	public String toString() {
		return mScopes.toString();
	}
}
