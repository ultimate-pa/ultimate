package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.HashMap;
import java.util.Map;

public class Multimap3<K1, K2, V> {
	
	Map<K1, Map<K2, V>> m_K1ToK2ToV = new HashMap<K1, Map<K2, V>>();
	
	public V put(K1 key1, K2 key2, V value) {
		Map<K2, V> k2toV = m_K1ToK2ToV.get(key1);
		if (k2toV == null) {
			k2toV = new HashMap<>();
			m_K1ToK2ToV.put(key1, k2toV);
		}
		return k2toV.put(key2, value);
	}
	
	public V get(K1 key1, K2 key2) {
		Map<K2, V> k2toV = m_K1ToK2ToV.get(key1);
		if (k2toV == null) {
			return null;
		} else {
			return k2toV.get(key2);
		}
	}
	

}
