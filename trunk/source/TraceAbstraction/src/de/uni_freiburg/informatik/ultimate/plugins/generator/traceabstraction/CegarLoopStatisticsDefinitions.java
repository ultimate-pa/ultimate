package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public enum CegarLoopStatisticsDefinitions implements IStatisticsElement {

	Result(Result.class, CegarLoopStatisticsDefinitions.DEFAULT_AGGREGATION_FUN, AStatisticsType.s_DataBeforeKey),

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
	private static final Function<Object, Function<Object, Object>> DEFAULT_AGGREGATION_FUN =
			x -> y -> CegarLoopStatisticsDefinitions.aggregateResult(x, y);

	CegarLoopStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
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