package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

public abstract class StatisticsType<T extends Enum<T> & IStatisticsElement> implements IStatisticsType {

	public static final Function<Object, Function<Object, Object>> INTEGER_ADDITION =
			x -> y -> (Integer) x + (Integer) y;
	public static final Function<Object, Function<Object, Object>> LONG_ADDITION = x -> y -> (Long) x + (Long) y;
	public static final Function<Object, Function<Object, Object>> IN_CA_RE_ADDITION = x -> y -> {
		((InCaReCounter) x).add((InCaReCounter) y);
		return x;
	};
	public static final Function<Object, Function<Object, Object>> DOUBLE_ADDITION = x -> y -> (Double) x + (Double) y;
	public static final Function<Object, Function<Object, Object>> STATISTICS_DATA_AGGREGATION = x -> y -> {
		((StatisticsData) x).aggregateBenchmarkData((StatisticsData) y);
		return x;
	};
	public static final Function<String, Function<Object, String>> KEY_BEFORE_DATA = key -> data -> key + ": " + data;
	public static final Function<String, Function<Object, String>> DATA_BEFORE_KEY =
			key -> data -> String.valueOf(data) + ' ' + key;
	public static final Function<String, Function<Object, String>> NANOS_BEFORE_KEY =
			key -> time -> prettyprintNanoseconds((Long) time) + " " + key;
	public static final Function<String, Function<Object, String>> KEY_BEFORE_NANOS =
			key -> time -> key + ": " + prettyprintNanoseconds((Long) time);
	public static final Function<Object, Function<Object, Object>> INTEGER_MAX =
			x -> y -> Math.max((Integer) x, (Integer) y);

	private final Class<T> mKeyType;

	public StatisticsType(final Class<T> keyType) {
		super();
		mKeyType = keyType;
	}

	@Override
	public Collection<String> getKeys() {
		final List<String> result = new ArrayList<>();
		for (final Enum<?> test : mKeyType.getEnumConstants()) {
			result.add(test.toString());
		}
		return result;
	}

	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		final T keyEnum = Enum.valueOf(mKeyType, key);
		return keyEnum.aggregate(value1, value2);
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		return prettyprintBenchmarkData(getKeys(), mKeyType, benchmarkData);
	}

	public static <T extends Enum<T> & IStatisticsElement> String prettyprintBenchmarkData(
			final Collection<String> keys, final Class<T> keyType, final IStatisticsDataProvider benchmarkData) {
		final StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (final String key : keys) {
			if (first) {
				first = false;
			} else {
				sb.append(", ");
			}
			final Object value = benchmarkData.getValue(key);
			final T keyE = Enum.valueOf(keyType, key);
			sb.append(keyE.prettyprint(value));
		}
		return sb.toString();
	}

	public static String prettyprintBenchmarkData(final String key, final IStatisticsDataProvider benchmarkData) {
		return key + " " + benchmarkData.getValue(key);
	}

	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1_000_000_000;
		final long tenthDigit = time / 100_000_000 % 10;
		return seconds + "." + tenthDigit + "s";
	}

}
