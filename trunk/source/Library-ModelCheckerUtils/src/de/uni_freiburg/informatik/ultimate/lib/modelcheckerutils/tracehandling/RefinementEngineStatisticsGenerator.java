/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * {@link IStatisticsDataProvider} that accumulates statistics from the various trace checks, interpolant generators,
 * etc. used during a run of a refinement engine.
 *
 * It avoids aggregating the same object twice by hashing all statistics during a refinement engine run and aggregating
 * only at the end.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RefinementEngineStatisticsGenerator implements IStatisticsDataProvider {

	private final ConstructionCache<RefinementEngineStatisticsDefinitions, Set<IStatisticsDataProvider>> mStats;
	private final ConstructionCache<RefinementEngineStatisticsDefinitions, StatisticsData> mStatsAggregated;
	private static final StatisticsType<RefinementEngineStatisticsDefinitions> TYPE =
			new StatisticsType<>(RefinementEngineStatisticsDefinitions.class);

	public RefinementEngineStatisticsGenerator() {
		mStats = new ConstructionCache<>(a -> new HashSet<>());
		mStatsAggregated = new ConstructionCache<>(a -> new StatisticsData());
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return TYPE;
	}

	/**
	 * Signal that the refinement engine has finished executing and all collected statistics should be aggregated now.
	 */
	public void finishRefinementEngineRun() {
		for (final Entry<RefinementEngineStatisticsDefinitions, Set<IStatisticsDataProvider>> entry : mStats
				.entrySet()) {
			final StatisticsData aggregatedData = mStatsAggregated.getOrConstruct(entry.getKey());
			for (final IStatisticsDataProvider data : entry.getValue()) {
				aggregatedData.aggregateBenchmarkData(data);
			}
		}
	}

	/**
	 * Add a new {@link IStatisticsDataProvider} of the <code>defs</code> type to this aggregator.
	 *
	 * @param defs
	 *            The type of statistics to aggregate
	 * @param stats
	 *            The actual data provider.
	 */
	public void addStatistics(final RefinementEngineStatisticsDefinitions defs, final IStatisticsDataProvider stats) {
		if (stats == null) {
			return;
		}
		mStats.getOrConstruct(defs).add(stats);
	}

	@Override
	public Object getValue(final String key) {
		final RefinementEngineStatisticsDefinitions keyEnum = RefinementEngineStatisticsDefinitions.valueOf(key);
		return mStatsAggregated.getOrConstruct(keyEnum);
	}

	@Override
	public Collection<String> getKeys() {
		return TYPE.getKeys();
	}

	public enum RefinementEngineStatisticsDefinitions implements IStatisticsElement {

		TRACE_CHECK(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

		INVARIANT_SYNTHESIS(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		INTERPOLANT_CONSOLIDATION(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		ABSTRACT_INTERPRETATION(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		PDR(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

		ACCELERATED_INTERPOLATION(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		SIFA(StatisticsData.class, StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA);

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		RefinementEngineStatisticsDefinitions(final Class<?> clazz,
				final Function<Object, Function<Object, Object>> aggr,
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
			return mPrettyprinter.apply(name()).apply(o);
		}
	}
}