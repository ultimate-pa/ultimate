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

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class CegarLoopStatisticsGenerator extends BaseStatisticsDataProvider {

	public static final String OverallTime = "OverallTime";
	public static final String OverallIterations = "OverallIterations";
	public static final String TraceHistogramMax = "TraceHistogramMax";
	public static final String AutomataDifferenceTime = "AutomataDifferenceTime";
	public static final String HoareTripleCheckerStatistics = "HoareTripleCheckerStatistics";
	public static final String PredicateUnifierStatistics = "PredicateUnifierStatistics";
	public static final String BiggestAbstraction = "BiggestAbstraction";
	public static final String TraceCheckStatistics = "TraceCheckStatistics";
	public static final String AutomataMinimizationStatistics = "AutomataMinimizationStatistics";
	public static final String REUSE_STATS = "ReuseStatistics";
	public static final String HOARE_ANNOTATION_STATS = "HoareAnnotationStatistics";

	@Reflected(prettyName = OverallTime)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mOverallTime = new TimeTracker();

	@Reflected(prettyName = OverallIterations)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mIterations;

	@Reflected(prettyName = TraceHistogramMax)
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mTraceHistogramMaximum = 0;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mInterpolantAutomatonStates;

	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mPathProgramHistogramMaximum;

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mEmptinessCheckTime = new TimeTracker();

	@Reflected(prettyName = AutomataDifferenceTime)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mAutomataDifferenceTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mDeadEndRemovalTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mHoareAnnotationTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mBasicInterpolantAutomatonTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mInitialAbstractionConstructionTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mDumpTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mPartialOrderReductionTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.BACKWARD_COVERING_INFORMATION)
	private final BackwardCoveringInformation mInterpolantCoveringCapability = new BackwardCoveringInformation(0, 0);

	@Reflected(prettyName = HoareTripleCheckerStatistics)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mEcData;

	@Reflected(prettyName = PredicateUnifierStatistics)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mPredicateUnifierData;

	@Reflected(prettyName = TraceCheckStatistics)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mTcData;

	@Reflected(prettyName = AutomataMinimizationStatistics)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mAmData;

	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mRefinementEngineStatistics;

	// manual declaration
	private SizeIterationPair mBiggestAbstraction = new SizeIterationPair(-1, -1);

	public CegarLoopStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
		mEcData = new StatisticsAggregator(storage);
		mPredicateUnifierData = new StatisticsAggregator(storage);
		mTcData = new StatisticsAggregator(storage);
		mAmData = new StatisticsAggregator(storage);
		mRefinementEngineStatistics = new StatisticsAggregator(storage);

		declare(BiggestAbstraction, () -> mBiggestAbstraction, SizeIterationPair.KEY_TYPE);
	}

	public void addEdgeCheckerData(final IStatisticsDataProvider ecbd) {
		mEcData.aggregateStatisticsData(ecbd);
	}

	public void addPredicateUnifierData(final IStatisticsDataProvider pubd) {
		mPredicateUnifierData.aggregateStatisticsData(pubd);
	}

	public void addTraceCheckData(final IStatisticsDataProvider tcbd) {
		mTcData.aggregateStatisticsData(tcbd);
	}

	public void addRefinementEngineStatistics(final IStatisticsDataProvider res) {
		mRefinementEngineStatistics.aggregateStatisticsData(res);
	}

	public void addAutomataMinimizationData(final IStatisticsDataProvider tcbd) {
		mAmData.aggregateStatisticsData(tcbd);
	}

	public void announceNextIteration() {
		mIterations++;
	}

	/**
	 * @return true iff size is the new maximum
	 */
	public boolean reportAbstractionSize(final int size, final int iteration) {
		if (size > mBiggestAbstraction.getSize()) {
			mBiggestAbstraction = new SizeIterationPair(size, iteration);
			return true;
		}
		return false;
	}

	public void reportTraceHistogramMaximum(final int maxCurrentTrace) {
		if (maxCurrentTrace > mTraceHistogramMaximum) {
			mTraceHistogramMaximum = maxCurrentTrace;
		}
	}

	public void reportPathProgramHistogramMaximum(final int pathProgramHistogramMax) {
		if (pathProgramHistogramMax > mPathProgramHistogramMaximum) {
			mPathProgramHistogramMaximum = pathProgramHistogramMax;
		}
	}

	public void reportInterpolantAutomatonStates(final int count) {
		mInterpolantAutomatonStates += count;
	}

	public void startDumpTime() {
		mDumpTime.start();
	}

	public void stopDumpTime() {
		mDumpTime.stop();
	}

	public void startInitialAbstractionConstructionTime() {
		mInitialAbstractionConstructionTime.start();
	}

	public void stopInitialAbstractionConstructionTime() {
		mInitialAbstractionConstructionTime.stop();
	}

	public void startOverallTime() {
		mOverallTime.start();
	}

	public void stopOverallTime() {
		mOverallTime.stop();
	}

	public void stopAutomataDifferenceTime() {
		mAutomataDifferenceTime.stop();
	}

	public void startAutomataDifferenceTime() {
		mAutomataDifferenceTime.start();
	}

	public void startPartialOrderReductionTime() {
		mPartialOrderReductionTime.start();
	}

	public void stopPartialOrderReductionTime() {
		mPartialOrderReductionTime.stop();
	}

	public void startEmptinessCheckTime() {
		mEmptinessCheckTime.start();
	}

	public void stopEmptinessCheckTime() {
		mEmptinessCheckTime.stop();
	}

	public void startHoareAnnotationTime() {
		mHoareAnnotationTime.start();
	}

	public void stopHoareAnnotationTime() {
		mHoareAnnotationTime.stop();
	}

}
