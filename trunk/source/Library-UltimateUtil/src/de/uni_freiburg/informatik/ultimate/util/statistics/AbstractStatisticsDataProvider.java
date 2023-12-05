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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * A base class for statistics providers. Subclasses can easily declare new data fields. A corresponding
 * {@link IStatisticsType} instance is created automatically.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public abstract class AbstractStatisticsDataProvider implements IStatisticsDataProvider {
	private final Map<String, Supplier<Object>> mSuppliers = new LinkedHashMap<>();
	private final Map<String, BinaryOperator<Object>> mAggregators = new HashMap<>();
	private final Map<String, Function<Object, Object>> mConverters = new HashMap<>();
	private final Map<String, BiFunction<String, Object, String>> mPrinters = new HashMap<>();
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
	protected final void declare(final String key, final Supplier<Object> getter, final KeyType type) {
		declare(key, getter, type::aggregate, type::convert, type::prettyPrint);
	}

	protected final void declare(final String key, final Supplier<Object> getter,
			final BinaryOperator<Object> aggregator, final BiFunction<String, Object, String> printer) {
		declare(key, getter, aggregator, Function.identity(), printer);
	}

	protected final void declare(final String key, final Supplier<Object> getter,
			final BinaryOperator<Object> aggregator, final Function<Object, Object> converter,
			final BiFunction<String, Object, String> printer) {
		assert !mSuppliers.containsKey(key);
		assert getter != null;
		assert aggregator != null;
		assert printer != null;
		mSuppliers.put(key, getter);
		mAggregators.put(key, aggregator);
		mConverters.put(key, converter);
		mPrinters.put(key, printer);
	}

	protected final void forward(final String key, final Supplier<IStatisticsDataProvider> statistics) {
		declare(key, () -> toStatisticsData(statistics.get()), Aggregate::statisticsDataAggregate,
				PrettyPrint::keyColonData);
	}

	protected final <T> void forwardAll(final String key, final Iterable<T> elems,
			final Function<T, IStatisticsDataProvider> getStatistics) {
		declare(key, () -> StreamSupport.stream(elems.spliterator(), false).map(getStatistics)
				.map(AbstractStatisticsDataProvider::toStatisticsData).collect(Collectors.toCollection(ArrayList::new)),
				Aggregate::appendList, PrettyPrint.list(PrettyPrint::keyColonData, Object::toString));
	}

	private static StatisticsData toStatisticsData(final IStatisticsDataProvider statistics) {
		final StatisticsData data = new StatisticsData();
		data.aggregateBenchmarkData(statistics);
		return data;
	}

	@Override
	public Object getValue(final String key) {
		final Supplier<Object> getter = mSuppliers.get(key);
		if (getter == null) {
			throw new IllegalArgumentException("Unknown key '" + key + "'");
		}
		final var rawValue = getter.get();

		final var converter = mConverters.get(key);
		if (converter == null) {
			return rawValue;
		}
		return converter.apply(rawValue);
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return mBenchmarkType;
	}

	@Override
	public String toString() {
		return mBenchmarkType.prettyprintBenchmarkData(this);
	}

	private class BenchmarkType implements IStatisticsType {

		@Override
		public Collection<String> getKeys() {
			return mSuppliers.keySet();
		}

		@Override
		public Object aggregate(final String key, final Object value1, final Object value2) {
			final BinaryOperator<Object> aggregator = mAggregators.get(key);
			if (aggregator == null) {
				throw new IllegalArgumentException("Unknown key '" + key + "'");
			}
			return aggregator.apply(value1, value2);
		}

		@Override
		public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
			final StringBuilder sb = new StringBuilder();
			String delimiter = "";
			for (final String key : getKeys()) {
				sb.append(delimiter);
				final Object value = benchmarkData.getValue(key);
				final BiFunction<String, Object, String> printer = mPrinters.get(key);
				sb.append(printer.apply(key, value));
				delimiter = ", ";
			}
			return sb.toString();
		}

	}
}
