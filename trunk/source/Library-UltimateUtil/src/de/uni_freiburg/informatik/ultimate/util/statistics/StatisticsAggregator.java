package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class StatisticsAggregator extends AbstractStatisticsDataProvider {

	private final Map<String, KeyType> mKeyTypes;
	private final Map<String, Object> mValues;
	private final Set<String> mKnownTypes;

	public StatisticsAggregator() {
		mKnownTypes = new HashSet<>();
		mValues = new LinkedHashMap<>();
		mKeyTypes = new HashMap<>();
	}

	public void aggregateBenchmarkData(final IStatisticsDataProvider sdp) {
		aggregateBenchmarkData("", sdp);
	}

	public void aggregateBenchmarkData(final String keyPrefix, final IStatisticsDataProvider sdp) {
		if (sdp instanceof StatisticsAggregator) {
			final StatisticsAggregator other = (StatisticsAggregator) sdp;
			mKnownTypes.addAll(other.mKnownTypes);
			for (final Entry<String, KeyType> entry : other.mKeyTypes.entrySet()) {
				final KeyType old = mKeyTypes.put(entry.getKey(), entry.getValue());
				if (old != null && old != entry.getValue()) {
					throw new UnsupportedOperationException("Conflicting keytypes");
				}
				if (old == null) {
					final var type = entry.getValue();
					declare(entry.getKey(), () -> mValues.get(entry.getKey()), type::aggregate, null,
							type::prettyPrint);
				}
			}

			for (final Entry<String, Object> entry : other.mValues.entrySet()) {
				final String key = entry.getKey();
				final KeyType type = mKeyTypes.get(entry.getKey());
				final Object val = mValues.computeIfAbsent(key, k -> type.createEmpty());
				mValues.put(key, type.aggregate(val, entry.getValue()));
			}
			return;
		}

		final List<Field> statFields = ReflectionUtil.instanceFields(sdp).stream()
				.filter(f -> f.getAnnotation(Statistics.class) != null).collect(Collectors.toList());
		final String sdpType = keyPrefix + sdp.getClass();
		if (mKnownTypes.add(sdpType)) {
			declareTypes(keyPrefix, statFields);
		}
		for (final Field f : statFields) {
			final Statistics annot = f.getAnnotation(Statistics.class);
			final String key = getKey(keyPrefix, f);
			final KeyType type = annot.type();
			final Object rawValue = ReflectionUtil.access(sdp, f);
			final Object newValue = type.aggregate(mValues.get(key), type.convert(rawValue));
			mValues.put(key, newValue);
		}
	}

	private void declareTypes(final String keyPrefix, final List<Field> statFields) {
		for (final Field f : statFields) {
			final Statistics annot = f.getAnnotation(Statistics.class);
			final String newKey = getKey(keyPrefix, f);
			final KeyType type = annot.type();
			final KeyType old = mKeyTypes.put(newKey, type);
			if (old != null && old != type) {
				throw new UnsupportedOperationException("Conflicting keytypes");
			}
			declare(newKey, () -> mValues.get(newKey), type);
			mValues.put(newKey, type.createEmpty());
		}
	}

	private String getKey(final String prefix, final Field f) {
		if (prefix == null || prefix == "") {
			return ReflectionUtil.fieldPrettyName(f);
		}
		return prefix + "+" + ReflectionUtil.fieldPrettyName(f);
	}

	@Retention(RetentionPolicy.RUNTIME)
	@Target(ElementType.FIELD)
	public @interface Statistics {
		KeyType type();
	}

}