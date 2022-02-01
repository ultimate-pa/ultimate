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
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Default implementation for objects that store benchmark data.
 *
 * @author Matthias Heizmann
 */
public class StatisticsData implements IStatisticsDataProvider, ICsvProviderProvider<Object> {
	private final Map<String, Object> mKey2Value = new HashMap<>();
	private IStatisticsType mBenchmarkType;

	/**
	 * Aggregate the benchmark data of this object and another IBenchmarkDataProvider. The aggregated data is stored in
	 * this object. Both objects have to have the same IBenchmarkType.
	 */
	public void aggregateBenchmarkData(final IStatisticsDataProvider benchmarkDataProvider) {
		if (mBenchmarkType == null) {
			assert mKey2Value.isEmpty() : "may not contain data if type is not known";
			mBenchmarkType = benchmarkDataProvider.getBenchmarkType();
			if (mBenchmarkType == null) {
				return;
			}
			for (final String key : mBenchmarkType.getKeys()) {
				final Object value = benchmarkDataProvider.getValue(key);
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
			// TODO: maybe we want to allow different types and only the keys
			// have to be the same...
			if (mBenchmarkType != benchmarkDataProvider.getBenchmarkType()) {
				throw new AssertionError("incompatible benchmarks");
			}
			for (final String key : mBenchmarkType.getKeys()) {
				final Object valueThis = mKey2Value.get(key);
				final Object valueOther = benchmarkDataProvider.getValue(key);
				final Object aggregatedValue = mBenchmarkType.aggregate(key, valueThis, valueOther);
				mKey2Value.put(key, aggregatedValue);
			}
		}
	}

	@Override
	public Object getValue(final String key) {
		final Object data = mKey2Value.get(key);
		if (data == null) {
			throw new IllegalArgumentException("No value for " + key + " available");
		}
		return data;
	}

	@Override
	public String toString() {
		if (mBenchmarkType == null) {
			return "No data available";
		}
		return mBenchmarkType.prettyprintBenchmarkData(this);
	}

	@Override
	public Collection<String> getKeys() {
		if (mBenchmarkType == null) {
			throw new AssertionError("BenchmarkData not yet initialized");
		}
		return mBenchmarkType.getKeys();
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return mBenchmarkType;
	}

	public boolean isEmpty() {
		return mKey2Value.isEmpty();
	}

	/**
	 * Returns the map from keys to values with the following modification: Each pair (k,v) where the value v is an
	 * IBenchmarkDataProvider is omitted. Instead, we add the set of pairs {(k + "_" + k_1, v_1),..., (k + "_" + k_n,
	 * v_n)} where (v_1,k_1), ..., (v_n,k_n) are the key value pairs of IBenchmarkDataProvider v. This modification is
	 * applied recursively. This method does not modify the original data.
	 */
	public Map<String, Object> getFlattenedKeyValueMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		for (final String key : getKeys()) {
			final Object value = getValue(key);
			if (value instanceof IStatisticsDataProvider) {
				if (value instanceof StatisticsData) {
					final StatisticsData statData = (StatisticsData) value;
					if (statData.isEmpty()) {
						// do nothing
					} else {
						final Map<String, Object> flattenedKeyValueMap = statData.getFlattenedKeyValueMap();
						for (final Entry<String, Object> entry : flattenedKeyValueMap.entrySet()) {
							final String composedKey = key + "_" + entry.getKey();
							result.put(composedKey, entry.getValue());
						}
					}
				} else {
					IStatisticsDataProvider sdProvider = (IStatisticsDataProvider) value;
					for (final String subKey : sdProvider.getKeys()) {
						final Object subValue = sdProvider.getValue(subKey);
						final String composedKey = key + "_" + subKey;
						result.put(composedKey, subValue);
					}
				}
			} else {
				result.put(key, value);
			}
		}
		return result;
	}

	@Override
	public ICsvProvider<Object> createCsvProvider() {
		final Map<String, Object> flatKeyValueMap = getFlattenedKeyValueMap();
		return CsvUtils.constructCvsProviderFromMap(flatKeyValueMap);
	}
}
