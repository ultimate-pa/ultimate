package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Default implementation for objects that store benchmark data.
 * @author Matthias Heizmann
 */
public class BenchmarkData implements IBenchmarkDataProvider {
	private final Map<String, Object> m_Key2Value = new HashMap<String, Object>();
	private IBenchmarkType m_BenchmarkType;
	
	/**
	 * Aggregate the benchmark data of this object and another 
	 * IBenchmarkDataProvider. The aggregated data is stored in this object.
	 * Both objects have to have the same IBenchmarkType.
	 */
	public void aggregateBenchmarkData(IBenchmarkDataProvider benchmarkDataProvider) {
		if (m_BenchmarkType == null) {
			assert m_Key2Value.isEmpty() : "may not contain data if type is not known";
			m_BenchmarkType = benchmarkDataProvider.getBenchmarkType();
			for (String key : m_BenchmarkType.getKeys()) {
				Object value = benchmarkDataProvider.getValue(key);
				// TODO: maybe we want to allow null values
				if (value == null) {
					throw new AssertionError("no value for " + key + " provided");
				}
				m_Key2Value.put(key, value);
			}
		} else {
			//TODO: maybe we want to allow different types and only the keys
			// have to be the same...
			if (m_BenchmarkType != benchmarkDataProvider.getBenchmarkType()) {
				throw new AssertionError("incompatible benchmarks");
			}
			for (String key : m_BenchmarkType.getKeys()) {
				Object valueThis = m_Key2Value.get(key);
				Object valueOther = benchmarkDataProvider.getValue(key);
				Object aggregatedValue = m_BenchmarkType.aggregate(key, valueThis, valueOther);
				m_Key2Value.put(key, aggregatedValue);
			}
		}
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider#getData(java.lang.String)
	 */
	@Override
	public Object getValue(String key) {
		Object data = m_Key2Value.get(key);
		if (data == null) {
			throw new IllegalArgumentException("No value for " + key + " available");
		}
		return data;
	}
	
	@Override
	public String toString() {
		if (m_BenchmarkType == null) {
			return "No data available";
		} else {
			return m_BenchmarkType.prettyprintBenchmarkData(this);
		}
	}

	@Override
	public Collection<String> getKeys() {
		if (m_BenchmarkType == null) {
			throw new AssertionError("BenchmarkData not yet initialized");
		} else {
			return m_BenchmarkType.getKeys();
		}
	}

	@Override
	public IBenchmarkType getBenchmarkType() {
		return m_BenchmarkType;
	}
	
	public boolean isEmpty() {
		return m_Key2Value.isEmpty();
	}
	
	/**
	 * Returns the map from keys to values with the following modification:
	 * Each pair (k,v) where the value v is an IBenchmarkDataProvider is
	 * omitted. Instead, we add the set of pairs {(k + "_" + k_1, v_1),..., 
	 * (k + "_" + k_n, v_n)} where (v_1,k_1), ..., (v_n,k_n) are the key
	 * value pairs of IBenchmarkDataProvider v.
	 * This modification is applied recursively. This method does not modify
	 * the original data.
	 */
	public LinkedHashMap<String, Object> getFlattenedKeyValueMap() {
		LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		for(String key : getKeys()) {
			Object value = getValue(key);
			if (value instanceof BenchmarkData) {
				if (((BenchmarkData) value).isEmpty()) {
					// do nothing
				} else {
					LinkedHashMap<String, Object> FlattenedKeyValueMap = 
							((BenchmarkData) value).getFlattenedKeyValueMap();
					for (Entry<String, Object> entry : FlattenedKeyValueMap.entrySet()) {
						String composedKey = key + "_" + entry.getKey();
						result.put(composedKey, entry.getValue());
					}
				}
			} else {
				result.put(key, value);
			}
		}
		return result;
	}
}
