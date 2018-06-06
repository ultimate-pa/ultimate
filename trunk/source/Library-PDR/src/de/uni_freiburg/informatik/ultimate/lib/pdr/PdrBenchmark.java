/*
 * Copyright (C) 2018 Jonas Werner (jonaswerner95@gmail.com)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PDR library .
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PDR library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PDR library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pdr;

import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public final class PdrBenchmark extends StatisticsGeneratorWithStopwatches implements IStatisticsDataProvider {

	private static final String[] STOPWATCHES = new String[] { PdrStatisticsDefinitions.PDR_RUNTIME.toString() };

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final PdrStatisticsDefinitions keyEnum = Enum.valueOf(PdrStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case PDR_RUNTIME:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		default:
			throw new AssertionError("unknown data: " + keyEnum);
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return PdrStatisticsType.getInstance();
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
	public enum PdrStatisticsDefinitions implements IStatisticsElement {
		PDR_RUNTIME(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY);

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		PdrStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
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

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class PdrStatisticsType extends StatisticsType<PdrStatisticsDefinitions> {

		private static final PdrStatisticsType INSTANCE = new PdrStatisticsType();

		public PdrStatisticsType() {
			super(PdrStatisticsDefinitions.class);
		}

		public static PdrStatisticsType getInstance() {
			return INSTANCE;
		}
	}

}