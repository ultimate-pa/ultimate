/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import java.util.Map;
import java.util.function.Supplier;

/**
 * A base class for statistics providers. Subclasses can easily declare new data fields. A corresponding
 * {@link IStatisticsType} instance is created automatically.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public abstract class AbstractStatisticsDataProvider implements IStatisticsDataProvider {

	private final Map<String, Supplier<Object>> mSuppliers = new HashMap<>();
	private final Map<String, KeyType> mTypes = new HashMap<>();
	private final BenchmarkType mBenchmarkType = new BenchmarkType();

	/**
	 * This method should be called in subclass constructors to declare data fields to be collected.
	 *
	 * @param key
	 *            The key identifying the field
	 * @param getter
	 *            A function that is called to retrieve the current value.
	 * @param type
	 *            The type of data (including aggregation and printing)
	 */
	protected void declare(final String key, final Supplier<Object> getter, final KeyType type) {
		assert !mSuppliers.containsKey(key);
		assert getter != null;
		assert type != null;
		mSuppliers.put(key, getter);
		mTypes.put(key, type);
	}

	@Override
	public Object getValue(final String key) {
		final Supplier<Object> getter = mSuppliers.get(key);
		if (getter == null) {
			throw new IllegalArgumentException("Unknown key '" + key + "'");
		}
		return getter.get();
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return mBenchmarkType;
	}

	private class BenchmarkType implements IStatisticsType {

		@Override
		public Collection<String> getKeys() {
			return mSuppliers.keySet();
		}

		@Override
		public Object aggregate(final String key, final Object value1, final Object value2) {
			final KeyType type = mTypes.get(key);
			if (type == null) {
				throw new IllegalArgumentException("Unknown key '" + key + "'");
			}
			return type.aggregate(value1, value2);
		}

		@Override
		public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
			final StringBuilder sb = new StringBuilder();
			String delimiter = "";
			for (final String key : getKeys()) {
				sb.append(delimiter);
				final Object value = benchmarkData.getValue(key);
				final KeyType type = mTypes.get(key);
				sb.append(type.prettyPrint(key, value));
				delimiter = ", ";
			}
			return sb.toString();
		}

	}
}
