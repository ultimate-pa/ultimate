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

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.MeasurementModifiedAfterCloseException;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.MeasurementsAddedAfterCloseException;
import de.uni_freiburg.informatik.ultimate.util.statistics.exception.MeasurementsRemovedAfterCloseException;

/**
 * A {@link StatisticsAggregator} allows you to combine arbitrary {@link IStatisticsDataProvider} into one
 * {@link IStatisticsDataProvider} instance.
 * 
 * You cannot subclass this class because it assumes that all metrics are stored inside this class. You would need to
 * extend measures with setters.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class StatisticsAggregator extends BaseStatisticsDataProvider {

	private final Map<String, Object> mValues;

	/**
	 * Create an empty {@link StatisticsAggregator} that does not auto-close.
	 */
	public StatisticsAggregator() {
		this(null, null);
	}

	/**
	 * Create an empty {@link StatisticsAggregator} that auto-closes at plugin-boundaries.
	 */
	public StatisticsAggregator(final IToolchainStorage storage) {
		this(storage, PLUGIN_STATISTICS_MARKER);
	}

	/**
	 * Create an empty {@link StatisticsAggregator} that uses the auto-close behavior of <tt>sdp</tt>.
	 */
	public StatisticsAggregator(final BaseStatisticsDataProvider sdp) {
		this(sdp.getStorage(), sdp.getMarker());
	}

	/**
	 * Create an empty {@link StatisticsAggregator} that auto-closes when the given marker is removed.
	 */
	public StatisticsAggregator(final IToolchainStorage storage, final Object marker) {
		super(storage, marker);
		mValues = new LinkedHashMap<>();
	}

	@Override
	public Object getValue(final String key) {
		final Object value = mValues.get(key);
		if (value == null) {
			throw new IllegalArgumentException("Unknown key '" + key + "'");
		}
		mWatcher.notifyRead(key);
		return value;
	}

	/**
	 * Aggregate all metrics of a {@link IStatisticsDataProvider} into this one without any key prefix. If sdp uses
	 * {@link Statistics} for its metrics, this method also supports auto-declaration.
	 *
	 * @param sdp
	 *            another {@link IStatisticsDataProvider}
	 */
	public void aggregateStatisticsData(final IStatisticsDataProvider sdp) {
		aggregateStatisticsData("", sdp);
	}

	/**
	 * Aggregate all metrics from another {@link IStatisticsDataProvider} or merge with another
	 * {@link StatisticsAggregator} using a certain prefix for each key. This allows you to combine the same provider
	 * for different applications without merging the values.
	 *
	 * @param keyPrefix
	 *            A prefix for the key
	 * @param other
	 *            another {@link IStatisticsDataProvider}
	 */
	public void aggregateStatisticsData(final String keyPrefix, final IStatisticsDataProvider other) {
		if (this == other) {
			throw new IllegalArgumentException("Cannot aggregate with itself");
		}

		for (final Entry<String, Measure> entry : other.getMeasures().entrySet()) {
			final String otherKey = entry.getKey();
			final String newKey;
			if (keyPrefix.length() == 0) {
				newKey = otherKey;
			} else {
				newKey = String.format("%s %s", keyPrefix, otherKey);
			}
			final Measure otherMeasure = entry.getValue();
			final MeasureDefinition otherDef = otherMeasure.getMeasureDefinition();
			final MeasureDefinition localDef = registerKeyIfNecessary(newKey, otherKey, otherMeasure);
			if (!otherDef.equals(localDef)) {
				throw new AssertionError();
			}
			// read local value directly and do not mark it as read
			final Object localVal = mValues.get(newKey);
			// read other value normally (marking it as read)
			final Object otherVal = other.getValue(otherKey);
			final Object newVal;
			if (localVal == null) {
				if (otherVal instanceof IStatisticsDataProvider) {
					// if measure is a nested data provider, read all its values in a fresh aggregator
					final StatisticsAggregator sa = new StatisticsAggregator(this);
					sa.aggregateStatisticsData((IStatisticsDataProvider) otherVal);
					newVal = sa;
				} else {
					newVal = otherVal;
				}
			} else {
				newVal = otherDef.aggregate(localVal, otherVal);
			}
			mValues.put(newKey, newVal);
		}
		other.close();
		// attach write watcher
		new StatisticsWriteWatcher(getStorage(), other);
	}

	private MeasureDefinition registerKeyIfNecessary(final String newKey, final String sdpKey,
			final Measure sdpMeasure) {
		final Measure local = getStat(newKey);
		if (local != null) {
			// already registered
			return local.getMeasureDefinition();
		}
		final MeasureDefinition other = sdpMeasure.getMeasureDefinition();
		declare(newKey, () -> mValues.get(newKey), other);
		return other;
	}

	/**
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	protected static final class StatisticsWriteWatcher implements IStorable {
		private static final AtomicLong NEXT_ID = new AtomicLong(0);
		private final long mId = NEXT_ID.getAndIncrement();
		private final IToolchainStorage mStorage;
		private final IStatisticsDataProvider mOriginal;
		private final StatisticsAggregator mShadow;

		public StatisticsWriteWatcher(final IToolchainStorage storage, final IStatisticsDataProvider sdp) {
			mStorage = storage;
			if (mStorage != null) {
				mStorage.putStorable(getStorageKey(), this);
			}
			mOriginal = sdp;
			mShadow = deepCopy(sdp);
		}

		private static StatisticsAggregator deepCopy(final IStatisticsDataProvider other) {
			// do not read watch this aggregator
			final StatisticsAggregator rtr = new StatisticsAggregator();
			for (final Entry<String, Measure> entry : other.getMeasures().entrySet()) {
				final String otherKey = entry.getKey();
				final Measure otherMeasure = entry.getValue();
				final MeasureDefinition otherDef = otherMeasure.getMeasureDefinition();

				// marking as read is ok, because we aggregated before
				final Object otherVal = other.getValue(otherKey);
				final Object copiedOtherVal;
				if (otherVal instanceof IStatisticsDataProvider) {
					// if measure is a nested data provider, create a deep copy of it as well
					copiedOtherVal = deepCopy((IStatisticsDataProvider) otherVal);
				} else {
					// TODO: extend write watching to other reference types by extending MeasureDefinition with a copy
					// operator ; move deepCopy there
					copiedOtherVal = otherVal;
				}
				rtr.declare(otherKey, () -> rtr.mValues.get(otherKey), otherDef);
				rtr.mValues.put(otherKey, copiedOtherVal);
			}
			return rtr;
		}

		@Override
		public void destroy() {
			if (mStorage != null) {
				mStorage.removeStorable(getStorageKey());
			}

			final Map<String, Measure> orgMeasures = mOriginal.getMeasures();
			final Map<String, Measure> shadowMeasures = mShadow.getMeasures();
			if (!orgMeasures.keySet().equals(shadowMeasures.keySet())) {
				final Set<String> added = DataStructureUtils.difference(orgMeasures.keySet(), shadowMeasures.keySet());
				if (!added.isEmpty()) {
					throw new MeasurementsAddedAfterCloseException(mOriginal, added);
				}
				final Set<String> removed =
						DataStructureUtils.difference(shadowMeasures.keySet(), orgMeasures.keySet());
				if (!removed.isEmpty()) {
					throw new MeasurementsRemovedAfterCloseException(mOriginal, removed);
				}
			}

			final Set<String> modifiedMeasures = new LinkedHashSet<>();
			for (final Entry<String, Measure> orgEntry : orgMeasures.entrySet()) {
				final Measure shadowMeasure = shadowMeasures.get(orgEntry.getKey());
				final Object orgValue = orgEntry.getValue().getGetter().get();
				final Object shadowValue = shadowMeasure.getGetter().get();
				// TODO: add equals function to MeasureDefinition to prevent false positives, in particular for
				// IStatisticsDataProvider
				if (!Objects.equals(orgValue, shadowValue)) {
					modifiedMeasures.add(orgEntry.getKey());
				}
			}

			if (!modifiedMeasures.isEmpty()) {
				throw new MeasurementModifiedAfterCloseException(mOriginal, modifiedMeasures);
			}
		}

		private String getStorageKey() {
			return StatisticsWriteWatcher.class.getSimpleName() + mId;
		}
	}
}