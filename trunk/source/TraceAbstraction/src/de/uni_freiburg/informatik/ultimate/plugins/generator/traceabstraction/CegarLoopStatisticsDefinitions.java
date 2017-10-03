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

	Result(Result.class, CegarLoopStatisticsUtils.DEFAULT_AGGREGATION_FUN, AStatisticsType.sDataBeforeKey),

	OverallTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	OverallIterations(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	TraceHistogramMax(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sDataBeforeKey),

	AutomataDifference(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	DeadEndRemovalTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	HoareAnnotationTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	HoareTripleCheckerStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),

	PredicateUnifierStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),

	BasicInterpolantAutomatonTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	BiggestAbstraction(Integer.class, CegarStatisticsType.s_SizeIterationPairDataAggregation,
			AStatisticsType.sKeyBeforeData),

	traceCheckStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),

	InterpolantConsolidationStatistics(StatisticsData.class,

			AStatisticsType.sStatisticsDataAggregation, AStatisticsType.sKeyBeforeData),
	PathInvariantsStatistics(StatisticsData.class,

			AStatisticsType.sStatisticsDataAggregation, AStatisticsType.sKeyBeforeData),

	InterpolantCoveringCapability(BackwardCoveringInformation.class, CoverageAnalysis.DEFAULT_AGGREGATION,
			AStatisticsType.sDataBeforeKey),

	TotalInterpolationStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),

	AbstIntTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	AbstIntIterations(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	AbstIntStrong(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),
	
	AutomataMinimizationStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),
	
	HoareAnnotationStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),
	
	RefinementEngineStatistics(StatisticsData.class, AStatisticsType.sStatisticsDataAggregation,
			AStatisticsType.sKeyBeforeData),
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