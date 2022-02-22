/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2022 University of Freiburg
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
/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.MeasurementNotReadyException;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.MeasurementUnreadException;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.StatisticsDataProviderAlreadyClosedException;

/**
 * A base class for statistics providers defined by {@link IStatisticsDataProvider}. Subclasses can easily declare new
 * data fields. A corresponding {@link IStatisticsType} instance is created automatically.
 *
 * This class ensures on {@link IStatisticsDataProvider#close()} that
 * <ol>
 * <li>{@link IStatisticsDataProvider#close()} was never called before,</li>
 * <li>that all metrics collected here are ready (as defined by {@link MeasureDefinition#isReady(Object)}, and</li>
 * <li>that all non-empty metric values have been read at least once.</li>
 * </ol>
 *
 * If subclasses supply an IToolchainStorage, this class will register itself with the storage and be closed at the end
 * of the storage life cycle if it was not closed before.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class BaseStatisticsDataProvider implements IStatisticsDataProvider {

	private final Map<String, Measure> mMeasures = new LinkedHashMap<>();
	protected final StatisticsReadWatcher mWatcher;

	/**
	 * Create a new {@link BaseStatisticsDataProvider}. If <tt>storage</tt> is not null, the instance will register
	 * itself with the storage and be closed after the {@link IStatisticsDataProvider#PLUGIN_STATISTICS_MARKER} is
	 * removed, i.e., at plugin boundaries.
	 *
	 * @param storage
	 *            A {@link IToolchainStorage} instance or null
	 */
	protected BaseStatisticsDataProvider(final IToolchainStorage storage) {
		this(storage, PLUGIN_STATISTICS_MARKER);
	}

	/**
	 * Create a new {@link BaseStatisticsDataProvider}. If <tt>storage</tt> is not null, the instance will register
	 * itself with the storage and be closed at the end of the {@link IToolchainStorage} life cycle. If <tt>marker</tt>
	 * is not null, the instance will register itself to the given marker.
	 *
	 * @param storage
	 *            A {@link IToolchainStorage} instance or null
	 * @param marker
	 *            An already pushed marker for {@link IToolchainStorage} or null
	 */
	protected BaseStatisticsDataProvider(final IToolchainStorage storage, final Object marker) {
		mWatcher = new StatisticsReadWatcher(storage, marker, this);
		autoDeclare();
	}

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
	protected final void declare(final String key, final Supplier<Object> getter, final MeasureDefinition type) {
		final Measure akt = new Measure(type, Objects.requireNonNull(getter));
		if (mMeasures.put(key, akt) != null) {
			throw new IllegalArgumentException(String.format("Key %s already registered", key));
		}
	}

	protected final void forward(final String key, final Supplier<IStatisticsDataProvider> statistics) {
		declare(key, () -> statistics.get(), MeasureDefinition.STATISTICS_AGGREGATOR);
	}

	protected final <T> void forwardAll(final String key, final Iterable<T> elems,
			final Function<T, IStatisticsDataProvider> getStatistics) {
		final MeasureDefinition type = MeasureDefinition.STATISTICS_AGGREGATOR;
		// Note: is never empty, this might produce spurious tests
		final MeasureDefinition kt = new MeasureDefinition(ArrayList::new, Aggregate::appendList,
				PrettyPrint.list(type::prettyPrint, Object::toString), Convert::identity, Test::alwaysReady,
				o -> false);
		declare(key, () -> StreamSupport.stream(elems.spliterator(), false).map(getStatistics).map(type::convert)
				.collect(Collectors.toCollection(ArrayList::new)), kt);
	}

	/**
	 * Helper to easily implement auto-declare in derived classes.
	 * 
	 * This method will {@link #declare(String, Supplier, MeasureDefinition)} a key for each field of the calling class
	 * that is annotated with the {@link Statistics} annotation. The key is defined by
	 * {@link ReflectionUtil#fieldPrettyName(java.lang.reflect.Field)}, i.e., it is either the actual name of the field,
	 * or the name specified by {@link Reflected#prettyName()}.
	 */
	private void autoDeclare() {
		getStatisticFields().entrySet().stream().forEachOrdered(e -> {
			final Field f = e.getValue();
			final String key = e.getKey();
			final MeasureDefinition annotType = f.getAnnotation(Statistics.class).type().keyType();
			declare(key, () -> ReflectionUtil.read(this, f), annotType);
		});
	}

	protected Map<String, Field> getStatisticFields() {
		return ReflectionUtil.instanceFields(getClass()).stream().filter(f -> f.getAnnotation(Statistics.class) != null)
				.collect(Collectors.toMap(ReflectionUtil::fieldPrettyName, f -> f, (e1, e2) -> {
					throw new IllegalArgumentException("Key used twice");
				}, LinkedHashMap::new));
	}

	/**
	 * Retrieve an {@link Measure} for a given key or null if the key does not exist. This allows you to, e.g., read or
	 * aggregate a metric without counting against the read-check of this class.
	 */
	protected final Measure getStat(final String key) {
		return mMeasures.get(key);
	}

	protected final Measure getStatChecked(final String key) {
		final Measure akt = mMeasures.get(key);
		if (akt == null) {
			throw new IllegalArgumentException(String.format("Unknown key '%s'", key));
		}
		return akt;
	}

	@Override
	public Object getValue(final String key) {
		final Measure akt = mMeasures.get(key);
		if (akt == null) {
			throw new IllegalArgumentException(String.format("Unknown key '%s'", key));
		}
		mWatcher.notifyRead(key);
		return akt.getGetter().get();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		String delimiter = "";
		for (final Entry<String, Measure> entry : getMeasures().entrySet()) {
			sb.append(delimiter);
			final Measure measure = entry.getValue();
			final MeasureDefinition type = measure.getMeasureDefinition();
			final Object value = measure.getGetter().get();
			sb.append(type.prettyPrint(entry.getKey(), type.convert(value)));
			delimiter = ", ";
		}
		return sb.toString();
	}

	@Override
	public void close() {
		mWatcher.destroy();
	}

	/**
	 * This method is a debug helper. With it, you can add breakpoints that watch for a certain ID of a
	 * {@link BaseStatisticsDataProvider}.
	 * 
	 * Do not use it for anything else.
	 */
	public boolean isId(final long id) {
		return mWatcher.mId == id;
	}

	protected void requireIsOpen() {
		mWatcher.requireIsOpen();
	}

	protected IToolchainStorage getStorage() {
		return mWatcher.getStorage();
	}

	protected Object getMarker() {
		return mWatcher.mMarker;
	}

	/**
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	protected static final class StatisticsReadWatcher implements IStorable {
		private static final AtomicLong NEXT_ID = new AtomicLong(0);
		private final long mId = NEXT_ID.getAndIncrement();
		private final IToolchainStorage mStorage;
		private final Object mMarker;

		private final String mCreationSignature;
		private final BaseStatisticsDataProvider mSDP;
		private final Set<String> mReadKeys;

		private boolean mIsClosed;

		public StatisticsReadWatcher(final BaseStatisticsDataProvider sdp) {
			this(null, null, sdp);
		}

		public StatisticsReadWatcher(final IToolchainStorage storage, final Object marker,
				final BaseStatisticsDataProvider sdp) {
			mIsClosed = false;
			mCreationSignature = ReflectionUtil.getCurrentCallStackOneLine();
			mSDP = sdp;
			mStorage = storage;
			mMarker = marker;
			mReadKeys = new HashSet<>();
			if (mStorage != null) {
				if (marker != null) {
					mStorage.putStorable(marker, getStorageKey(), this);
				} else {
					mStorage.putStorable(getStorageKey(), this);
				}
			}
		}

		public void notifyRead(final String key) {
			mReadKeys.add(key);
		}

		@Override
		public void destroy() {
			requireIsOpen();
			// Useful when looking at StatisticsDataProviderAlreadyClosedException
			System.out.println("Closing " + mId + " " + ReflectionUtil.getCurrentCallStackOneLine());
			if (mStorage != null) {
				mStorage.removeStorable(getStorageKey());
			}
			mIsClosed = true;

			final List<String> notReady = mSDP.mMeasures.entrySet().stream().filter(a -> isNotReady(a.getValue()))
					.map(Entry::getKey).collect(Collectors.toList());
			if (!notReady.isEmpty()) {
				throw new MeasurementNotReadyException(mSDP, mCreationSignature, mId, notReady);
			}
			final Set<String> unreadKeys = new LinkedHashSet<>();
			for (final String key : mSDP.mMeasures.keySet()) {
				if (mReadKeys.contains(key)) {
					continue;
				}
				final Measure akt = mSDP.mMeasures.get(key);
				final Object value = akt.getGetter().get();
				if (akt.getMeasureDefinition().isEmpty(value)) {
					continue;
				}
				unreadKeys.add(key + "=" + value);
			}

			if (!unreadKeys.isEmpty()) {
				throw new MeasurementUnreadException(mSDP, mCreationSignature, mId, unreadKeys);
			}
		}

		public void requireIsOpen() {
			if (mIsClosed) {
				throw new StatisticsDataProviderAlreadyClosedException(mSDP, mCreationSignature, mId);
			}
		}

		private static boolean isNotReady(final Measure akt) {
			return !akt.getMeasureDefinition().isReady(akt.getGetter().get());
		}

		private String getStorageKey() {
			return StatisticsReadWatcher.class.getSimpleName() + mId;
		}

		private IToolchainStorage getStorage() {
			return mStorage;
		}
	}

	@Override
	public Collection<String> getKeys() {
		return mMeasures.keySet();
	}

	@Override
	public Measure getMeasure(final String key) {
		return getStatChecked(key);
	}

	@Override
	public Map<String, Measure> getMeasures() {
		return Collections.unmodifiableMap(mMeasures);
	}

	/**
	 * Returns the map from keys to values with the following modification: Each pair (k,v) where the value v is an
	 * IBenchmarkDataProvider is omitted. Instead, we add the set of pairs {(k + "_" + k_1, v_1),..., (k + "_" + k_n,
	 * v_n)} where (v_1,k_1), ..., (v_n,k_n) are the key value pairs of IBenchmarkDataProvider v. This modification is
	 * applied recursively. This method does not modify the original data.
	 */
	private Map<String, Object> getFlattenedKeyValueMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		for (final String key : getKeys()) {
			final Object value = getValue(key);
			if (value instanceof IStatisticsDataProvider) {
				if (value instanceof BaseStatisticsDataProvider) {
					final BaseStatisticsDataProvider statData = (BaseStatisticsDataProvider) value;
					if (statData.mMeasures.isEmpty()) {
						// do nothing
					} else {
						final Map<String, Object> flattenedKeyValueMap = statData.getFlattenedKeyValueMap();
						for (final Entry<String, Object> entry : flattenedKeyValueMap.entrySet()) {
							final String composedKey = key + "_" + entry.getKey();
							result.put(composedKey, entry.getValue());
						}
					}
				} else {
					final IStatisticsDataProvider sdp = (IStatisticsDataProvider) value;
					for (final String subKey : sdp.getKeys()) {
						final Object subValue = sdp.getValue(subKey);
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

	/**
	 * The {@link Statistics} attribute allows you to annotate single metrics with their type, i.e., with which
	 * aggregation function and pretty print function they should be processed. Due to Java restrictions, they have to
	 * be combined in the {@link DefaultMeasureDefinitions} enum, which itself references to the actual definition
	 * {@link Byte} a {@link MeasureDefinition} object.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@Retention(RetentionPolicy.RUNTIME)
	@Target(ElementType.FIELD)
	public @interface Statistics {
		/**
		 * Provide access to the {@link MeasureDefinition} of a measure.
		 *
		 * @see MeasureDefinition
		 * @see DefaultMeasureDefinitions
		 */
		DefaultMeasureDefinitions type();
	}

}
