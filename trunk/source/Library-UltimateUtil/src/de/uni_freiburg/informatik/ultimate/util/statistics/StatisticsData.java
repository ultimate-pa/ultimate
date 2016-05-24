/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;

/**
 * Default implementation for objects that store benchmark data.
 * @author Matthias Heizmann
 */
public class StatisticsData implements IStatisticsDataProvider {
	private final Map<String, Object> mKey2Value = new HashMap<String, Object>();
	private IStatisticsType mBenchmarkType;
	
	/**
	 * Aggregate the benchmark data of this object and another 
	 * IBenchmarkDataProvider. The aggregated data is stored in this object.
	 * Both objects have to have the same IBenchmarkType.
	 */
	public void aggregateBenchmarkData(IStatisticsDataProvider benchmarkDataProvider) {
		if (mBenchmarkType == null) {
			assert mKey2Value.isEmpty() : "may not contain data if type is not known";
			mBenchmarkType = benchmarkDataProvider.getBenchmarkType();
			if (mBenchmarkType == null) {
				return;
			}
			for (String key : mBenchmarkType.getKeys()) {
				Object value = benchmarkDataProvider.getValue(key);
				// TODO: maybe we want to allow null values
				if (value == null) {
					throw new AssertionError("no value for " + key + " provided");
				}
				mKey2Value.put(key, value);
			}
		} else {
			if (benchmarkDataProvider.getBenchmarkType() == null) {
				return;
			}
			//TODO: maybe we want to allow different types and only the keys
			// have to be the same...
			if (mBenchmarkType != benchmarkDataProvider.getBenchmarkType()) {
				throw new AssertionError("incompatible benchmarks");
			}
			for (String key : mBenchmarkType.getKeys()) {
				Object valueThis = mKey2Value.get(key);
				Object valueOther = benchmarkDataProvider.getValue(key);
				Object aggregatedValue = mBenchmarkType.aggregate(key, valueThis, valueOther);
				mKey2Value.put(key, aggregatedValue);
			}
		}
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider#getData(java.lang.String)
	 */
	@Override
	public Object getValue(String key) {
		Object data = mKey2Value.get(key);
		if (data == null) {
			throw new IllegalArgumentException("No value for " + key + " available");
		}
		return data;
	}
	
	@Override
	public String toString() {
		if (mBenchmarkType == null) {
			return "No data available";
		} else {
			return mBenchmarkType.prettyprintBenchmarkData(this);
		}
	}

	@Override
	public Collection<String> getKeys() {
		if (mBenchmarkType == null) {
			throw new AssertionError("BenchmarkData not yet initialized");
		} else {
			return mBenchmarkType.getKeys();
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return mBenchmarkType;
	}
	
	public boolean isEmpty() {
		return mKey2Value.isEmpty();
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
			if (value instanceof IStatisticsDataProvider) {
				if (value instanceof StatisticsData) {
					if (((StatisticsData) value).isEmpty()) {
						// do nothing
					} else {
						LinkedHashMap<String, Object> FlattenedKeyValueMap = 
								((StatisticsData) value).getFlattenedKeyValueMap();
						for (Entry<String, Object> entry : FlattenedKeyValueMap.entrySet()) {
							String composedKey = key + "_" + entry.getKey();
							result.put(composedKey, entry.getValue());
						}
					}
				} else {
					for (String subKey : ((IStatisticsDataProvider) value).getKeys()) {
						Object subValue = ((IStatisticsDataProvider) value).getValue(subKey);
						String composedKey = key + "_" + subKey;
						result.put(composedKey, subValue);
					}
				}
			} else {
				result.put(key, value);
			}
		}
		return result;
	}
	
	
	public ICsvProvider<Object> createCvsProvider() {
		LinkedHashMap<String, Object> flatKeyValueMap = getFlattenedKeyValueMap();
		return CsvUtils.constructCvsProviderFromMap(flatKeyValueMap);
	}
}
