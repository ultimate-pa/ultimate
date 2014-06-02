package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

import java.util.HashMap;
import java.util.Map;

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
	public Iterable<String> getKeys() {
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
}
