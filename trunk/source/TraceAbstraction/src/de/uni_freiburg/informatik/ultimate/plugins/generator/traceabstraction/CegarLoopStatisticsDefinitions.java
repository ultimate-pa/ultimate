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

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public enum CegarLoopStatisticsDefinitions implements IStatisticsElement {

	Result(Result.class, CegarLoopStatisticsUtils.DEFAULT_AGGREGATION_FUN, AStatisticsType.s_DataBeforeKey),

	OverallTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	OverallIterations(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),

	TraceHistogramMax(Integer.class, AStatisticsType.s_IntegerMaximum, AStatisticsType.s_DataBeforeKey),

	AutomataDifference(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	DeadEndRemovalTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	HoareAnnotationTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	HoareTripleCheckerStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),

	PredicateUnifierStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),

	BasicInterpolantAutomatonTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	BiggestAbstraction(Integer.class, CegarStatisticsType.s_SizeIterationPairDataAggregation,
			AStatisticsType.s_KeyBeforeData),

	TraceCheckerStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),

	InterpolantConsolidationStatistics(StatisticsData.class,

			AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
	PathInvariantsStatistics(StatisticsData.class,

			AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),

	InterpolantCoveringCapability(BackwardCoveringInformation.class, CoverageAnalysis.DEFAULT_AGGREGATION,
			AStatisticsType.s_DataBeforeKey),

	TotalInterpolationStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),

	AbstIntTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),

	AbstIntIterations(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),

	AbstIntStrong(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),
	
	AutomataMinimizationStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),
	
	HoareAnnotationStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation,
			AStatisticsType.s_KeyBeforeData),
	;

	private final Class<?> mClazz;
	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;


	CegarLoopStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mClazz = Objects.requireNonNull(clazz);
		mAggr = Objects.requireNonNull(aggr);
		mPrettyprinter = Objects.requireNonNull(prettyprinter);
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(name()).apply(o);
	}

	@Override
	public Class<?> getDataType() {
		return mClazz;
	}

	public static AbstractCegarLoop.Result aggregateResult(final Object value1, final Object value2) {
		final AbstractCegarLoop.Result result1 = (AbstractCegarLoop.Result) value1;
		final AbstractCegarLoop.Result result2 = (AbstractCegarLoop.Result) value2;
		final Set<AbstractCegarLoop.Result> results = new HashSet<>();
		results.add(result1);
		results.add(result2);
		if (results.contains(AbstractCegarLoop.Result.UNSAFE)) {
			return AbstractCegarLoop.Result.UNSAFE;
		} else if (results.contains(AbstractCegarLoop.Result.UNKNOWN)) {
			return AbstractCegarLoop.Result.UNKNOWN;
		} else if (results.contains(AbstractCegarLoop.Result.TIMEOUT)) {
			return AbstractCegarLoop.Result.TIMEOUT;
		} else if (results.contains(AbstractCegarLoop.Result.SAFE)) {
			return AbstractCegarLoop.Result.SAFE;
		} else {
			throw new AssertionError();
		}
	}
}