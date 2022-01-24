
/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library.
 *
 * The ULTIMATE accelerated interpolation library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE accelerated interpolation library  is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE accelerated interpolation library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark;

import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Benchmark for evaluating the performance of the {@link AcceleratedInterpolation} paradigm.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AcceleratedInterpolationBenchmark extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	private static final String[] STOPWATCHES =
			new String[] { AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_CORE.toString(),
					AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_OVERALL.toString(),
					AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPDETECTOR.toString(),
					AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPACCELERATOR.toString() };

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final AcceleratedInterpolationStatisticsDefinitions keyEnum =
				Enum.valueOf(AcceleratedInterpolationStatisticsDefinitions.class, key);
		final String errorMsg = "clock still running: ";
		switch (keyEnum) {
		case ACCELINTERPOL_CORE:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError(errorMsg + key);
			}
		case ACCELINTERPOL_OVERALL:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError(errorMsg + key);
			}
		case ACCELINTERPOL_LOOPDETECTOR:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError(errorMsg + key);
			}
		case ACCELINTERPOL_LOOPACCELERATOR:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError(errorMsg + key);
			}
		default:
			throw new AssertionError("unknown data: " + keyEnum);
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return AccelInterpolStatisticsType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return STOPWATCHES;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum AcceleratedInterpolationStatisticsDefinitions implements IStatisticsElement {
		ACCELINTERPOL_CORE(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),
		ACCELINTERPOL_OVERALL(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),
		ACCELINTERPOL_LOOPDETECTOR(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),
		ACCELINTERPOL_LOOPACCELERATOR(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY);

		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		AcceleratedInterpolationStatisticsDefinitions(final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(CoreUtil.getUpperToCamelCase(name())).apply(o);
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class AccelInterpolStatisticsType
			extends StatisticsType<AcceleratedInterpolationStatisticsDefinitions> {

		private static final AccelInterpolStatisticsType INSTANCE = new AccelInterpolStatisticsType();

		AccelInterpolStatisticsType() {
			super(AcceleratedInterpolationStatisticsDefinitions.class);
		}

		public static AccelInterpolStatisticsType getInstance() {
			return INSTANCE;
		}
	}

}
