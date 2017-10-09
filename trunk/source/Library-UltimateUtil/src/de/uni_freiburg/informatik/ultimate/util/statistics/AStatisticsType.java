package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

public abstract class AStatisticsType<T extends Enum<T> & IStatisticsElement> implements IStatisticsType {

	public static Function<Object, Function<Object, Object>> sIntegerAddition = x -> y -> (Integer) x + (Integer) y;
	public static Function<Object, Function<Object, Object>> sLongAddition = x -> y -> (Long) x + (Long) y;
	public static Function<Object, Function<Object, Object>> sIncareAddition = x -> y -> {
		((InCaReCounter) x).add((InCaReCounter) y);
		return x;
	};
	public static Function<Object, Function<Object, Object>> sDoubleAddition = x -> y -> (Double) x + (Double) y;
	public static Function<Object, Function<Object, Object>> sStatisticsDataAggregation = x -> y -> {
		((StatisticsData) x).aggregateBenchmarkData((StatisticsData) y);
		return x;
	};
	public static Function<String, Function<Object, String>> sKeyBeforeData = key -> data -> key + ": " + data;
	public static Function<String, Function<Object, String>> sDataBeforeKey =
			key -> data -> String.valueOf(data) + ' ' + key;
	public static Function<String, Function<Object, String>> sTimeBeforeKey =
			key -> time -> prettyprintNanoseconds((Long) time) + " " + key;
	public static Function<Object, Function<Object, Object>> sIntegerMaximum =
			x -> y -> Math.max((Integer) x, (Integer) y);

	private final Class<T> mKeyType;

	public AStatisticsType(final Class<T> keyType) {
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
		final Object result = keyEnum.aggregate(value1, value2);
		return result;
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
