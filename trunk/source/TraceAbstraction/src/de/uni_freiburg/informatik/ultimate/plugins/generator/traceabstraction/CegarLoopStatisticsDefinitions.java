/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public enum CegarLoopStatisticsDefinitions implements IStatisticsElement {

	OverallTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	OverallIterations(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

	TraceHistogramMax(StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),

	PathProgramHistogramMax(StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),

	EmptinessCheckTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	AutomataDifference(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	DeadEndRemovalTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	HoareAnnotationTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	InitialAbstractionConstructionTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	HoareTripleCheckerStatistics(StatisticsType.STATISTICS_AGGREGATOR_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	PredicateUnifierStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	BasicInterpolantAutomatonTime(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),

	BiggestAbstraction(CegarStatisticsType.SIZE_ITERATION_PAIR_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	InterpolantAutomatonStates(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

	traceCheckStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	InterpolantConsolidationStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION,

			StatisticsType.KEY_BEFORE_DATA),
	PathInvariantsStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION,

			StatisticsType.KEY_BEFORE_DATA),

	InterpolantCoveringCapability(CoverageAnalysis.DEFAULT_AGGREGATION, StatisticsType.DATA_BEFORE_KEY),

	TotalInterpolationStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	DumpTime(StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),

	AutomataMinimizationStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	HoareAnnotationStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	RefinementEngineStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	ReuseStatistics(StatisticsType.STATISTICS_DATA_AGGREGATION, StatisticsType.KEY_BEFORE_DATA),

	ErrorAutomatonCreated(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA);

	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;

	CegarLoopStatisticsDefinitions(final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mAggr = Objects.requireNonNull(aggr);
		mPrettyprinter = Objects.requireNonNull(prettyprinter);
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(CoreUtil.getUpperToCamelCase(name())).apply(o);
	}

	public static AbstractCegarLoop.Result aggregateResult(final Object value1, final Object value2) {
		final AbstractCegarLoop.Result result1 = (AbstractCegarLoop.Result) value1;
		final AbstractCegarLoop.Result result2 = (AbstractCegarLoop.Result) value2;

		final Set<AbstractCegarLoop.Result> results = new HashSet<>();
		results.add(result1);
		results.add(result2);

		if (results.contains(AbstractCegarLoop.Result.UNSAFE)) {
			return AbstractCegarLoop.Result.UNSAFE;
		}
		if (results.contains(AbstractCegarLoop.Result.UNKNOWN)) {
			return AbstractCegarLoop.Result.UNKNOWN;
		}
		if (results.contains(AbstractCegarLoop.Result.TIMEOUT)) {
			return AbstractCegarLoop.Result.TIMEOUT;
		}
		if (DataStructureUtils.haveNonEmptyIntersection(AbstractCegarLoop.Result.USER_LIMIT_RESULTS, results)) {
			return DataStructureUtils.getSomeCommonElement(AbstractCegarLoop.Result.USER_LIMIT_RESULTS, results).get();
		}
		if (results.contains(AbstractCegarLoop.Result.SAFE)) {
			return AbstractCegarLoop.Result.SAFE;
		} else {
			throw new AssertionError();
		}
	}
}