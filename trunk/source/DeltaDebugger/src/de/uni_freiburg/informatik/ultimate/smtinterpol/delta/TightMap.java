package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A tight implementation of the Map interface.
 * @author Juergen Christ
 */
public class TightMap<K, V> implements Map<K, V> {

	private Map<K, V> m_Backing;
	
	public TightMap() {
		m_Backing = Collections.emptyMap();
	}
	
	@Override
	public int size() {
		return m_Backing.size();
	}

	@Override
	public boolean isEmpty() {
		return m_Backing.isEmpty();
	}

	@Override
	public boolean containsKey(Object key) {
		return m_Backing.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return m_Backing.containsValue(value);
	}

	@Override
	public V get(Object key) {
		return m_Backing.get(key);
	}

	@Override
	public V put(K key, V value) {
		if (m_Backing == Collections.emptyMap()) {
			m_Backing = Collections.singletonMap(key, value);
			return null;
		}
		if (!(m_Backing instanceof HashMap)) {
			// it is a singleton map...
			if (m_Backing.containsKey(key)) {
				// Replace
				V oldval = m_Backing.get(key);
				m_Backing = Collections.singletonMap(key, value);
				return oldval;
			}
			// We need at least two elements
			m_Backing = new HashMap<K, V>(m_Backing);
		}
		return m_Backing.put(key, value);
	}

	@Override
	public V remove(Object key) {
		if (m_Backing == Collections.emptyMap())
			return null;
		if (!(m_Backing instanceof HashMap)) {
			// It is a singleton map...
			if (m_Backing.containsKey(key)) {
				V oldVal = m_Backing.get(key);
				m_Backing = Collections.emptyMap();
				return oldVal;
			}
			return null;
		}
		V res = m_Backing.remove(key);
		if (m_Backing.size() == 1) {
			Map.Entry<K, V> me = m_Backing.entrySet().iterator().next();
			m_Backing = Collections.singletonMap(me.getKey(), me.getValue());
		}
		return res;
	}

	@Override
	public void putAll(Map<? extends K, ? extends V> m) {
		if (m.isEmpty())
			return;
		if (m.size() > 1) {
			if (!(m_Backing instanceof HashMap))
				m_Backing = new HashMap<K, V>(m_Backing);
			m_Backing.putAll(m);
		} else {
			Map.Entry<? extends K, ? extends V> me =
					m.entrySet().iterator().next();
			put(me.getKey(), me.getValue());
		}
	}

	@Override
	public void clear() {
		m_Backing = Collections.emptyMap();
	}

	@Override
	public Set<K> keySet() {
		return m_Backing.keySet();
	}

	@Override
	public Collection<V> values() {
		return m_Backing.values();
	}

	@Override
	public Set<java.util.Map.Entry<K, V>> entrySet() {
		return m_Backing.entrySet();
	}

}
