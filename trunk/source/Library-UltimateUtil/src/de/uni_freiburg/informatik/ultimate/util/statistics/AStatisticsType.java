package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

public abstract class AStatisticsType<T extends Enum<T> & IStatisticsElement> implements IStatisticsType {
	
	public static Function<Object, Function<Object,Object>> s_IntegerAddition = 
			x -> y -> (Integer) x + (Integer) y;
	public static Function<Object, Function<Object,Object>> s_LongAddition = 
			x -> y -> (Long) x + (Long) y;
	public static Function<Object, Function<Object,Object>> s_IncareAddition = 
			x -> y -> { ((InCaReCounter) x).add((InCaReCounter) y); return x;};
	public static Function<Object, Function<Object,Object>> s_StatisticsDataAggregation = 
			x -> y -> { ((StatisticsData) x).aggregateBenchmarkData((StatisticsData) y); return x;};
	public static Function<String, Function<Object,String>> s_KeyBeforeData = 
			key -> data -> key + ": " + String.valueOf(data);
	public static Function<String, Function<Object,String>> s_DataBeforeKey = 
			key -> data -> String.valueOf(data) + " " + key;
	public static Function<String, Function<Object,String>> s_TimeBeforeKey = 
			key -> time -> prettyprintNanoseconds( (Long) time) + " " + key;
	public static Function<Object, Function<Object,Object>> s_IntegerMaximum = 
			x -> y -> Math.max((Integer) x, (Integer) y);

	
	private final Class<T> mKeys;
	
	public AStatisticsType(final Class<T> keys) {
		super();
		mKeys = keys;
	}

	@Override
	public Collection<String> getKeys() {
		final List<String> result = new ArrayList<>();
		for (final Enum<?> test : mKeys.getEnumConstants()) {
			result.add(test.toString());
		}
		return result;
	}

	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		final T keyEnum = Enum.valueOf(mKeys, key);
		final Object result = keyEnum.aggregate(value1, value2);
		return result;
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		final StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (final String key : getKeys()) {
			if (first) {
				first = false;
			} else {
				sb.append(", ");
			}
			final Object value = benchmarkData.getValue(key);
			final T keyE = Enum.valueOf(mKeys, key);
			sb.append(keyE.prettyprint(value));
		}
		return sb.toString();
	}
	
	
	public static String prettyprintBenchmarkData(final String key, final IStatisticsDataProvider benchmarkData) {
		return key + " " + benchmarkData.getValue(key);
	}
	
	
	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1000000000;
		final long tenthDigit = (time / 100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

}
