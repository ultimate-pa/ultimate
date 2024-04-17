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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType.SizeIterationPair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

public class CegarLoopStatisticsGenerator extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	private final StatisticsData mReuseStats = new StatisticsData();
	private final StatisticsAggregator mEcData = new StatisticsAggregator();
	private final StatisticsData mPredicateUnifierData = new StatisticsData();
	private final StatisticsData mTcData = new StatisticsData();
	private final StatisticsData mTiData = new StatisticsData();
	private final StatisticsData mAmData = new StatisticsData();
	private final StatisticsData mHoareAnnotationData = new StatisticsData();
	private final StatisticsData mInterpolantConsolidationBenchmarks = new StatisticsData();
	private final StatisticsData mPathInvariantsStatistics = new StatisticsData();
	private final StatisticsData mRefinementEngineStatistics = new StatisticsData();
	private int mConditionalCommutativityIAIntegrations = 0;
	private int mConditionalCommutativityDFSRestarts = 0;
	private int mIterations = 0;
	private SizeIterationPair mBiggestAbstraction = new SizeIterationPair(-1, -1);
	private BackwardCoveringInformation mBCI = new BackwardCoveringInformation(0, 0);
	private int mTraceHistogramMaximum = 0;
	private int mInterpolantAutomatonStates = 0;
	private int mPathProgramHistogramMaximum = 0;

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}

	public void addReuseStats(final IStatisticsDataProvider reuseStats) {
		mReuseStats.aggregateBenchmarkData(reuseStats);
	}

	public void addEdgeCheckerData(final IStatisticsDataProvider ecbd) {
		mEcData.aggregateBenchmarkData(ecbd);
	}

	public void addPredicateUnifierData(final IStatisticsDataProvider pubd) {
		mPredicateUnifierData.aggregateBenchmarkData(pubd);
	}

	public void addTraceCheckData(final IStatisticsDataProvider tcbd) {
		mTcData.aggregateBenchmarkData(tcbd);
	}

	public void addRefinementEngineStatistics(final IStatisticsDataProvider res) {
		mRefinementEngineStatistics.aggregateBenchmarkData(res);
	}

	public void addTotalInterpolationData(final IStatisticsDataProvider tibd) {
		mTiData.aggregateBenchmarkData(tibd);
	}

	public void addBackwardCoveringInformation(final BackwardCoveringInformation bci) {
		mBCI = new BackwardCoveringInformation(mBCI, bci);
	}

	public void announceNextIteration() {
		mIterations++;
	}

	public void addAutomataMinimizationData(final IStatisticsDataProvider tcbd) {
		mAmData.aggregateBenchmarkData(tcbd);
	}

	public void addHoareAnnotationData(final IStatisticsDataProvider hasp) {
		mHoareAnnotationData.aggregateBenchmarkData(hasp);
	}
	
	public void addConditionalCommutativityIAIntegration() {
		mConditionalCommutativityIAIntegrations++;
	}
	
	public void addConditionalCommutativityDFSRestart() {
		mConditionalCommutativityDFSRestarts++;
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

	@Override
	public Object getValue(final String key) {
		final CegarLoopStatisticsDefinitions keyEnum = Enum.valueOf(CegarLoopStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case OverallTime:
		case EmptinessCheckTime:
		case AutomataDifference:
		case DeadEndRemovalTime:
		case HoareAnnotationTime:
		case BasicInterpolantAutomatonTime:
		case InitialAbstractionConstructionTime:
		case ConditionalCommutativityCheckTime:
		case DumpTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case HoareTripleCheckerStatistics:
			return mEcData;
		case ReuseStatistics:
			return mReuseStats;
		case PredicateUnifierStatistics:
			return mPredicateUnifierData;
		case traceCheckStatistics:
			return mTcData;
		case InterpolantConsolidationStatistics:
			return mInterpolantConsolidationBenchmarks;
		case PathInvariantsStatistics:
			return mPathInvariantsStatistics;
		case TotalInterpolationStatistics:
			return mTiData;
		case OverallIterations:
			return mIterations;
		case TraceHistogramMax:
			return mTraceHistogramMaximum;
		case PathProgramHistogramMax:
			return mPathProgramHistogramMaximum;
		case BiggestAbstraction:
			return mBiggestAbstraction;
		case InterpolantAutomatonStates:
			return mInterpolantAutomatonStates;
		case InterpolantCoveringCapability:
			return mBCI;
		case AutomataMinimizationStatistics:
			return mAmData;
		case HoareAnnotationStatistics:
			return mHoareAnnotationData;
		case RefinementEngineStatistics:
			return mRefinementEngineStatistics;
		case ConditionalCommutativityIAIntegrations:
			return mConditionalCommutativityIAIntegrations;
		case ConditionalCommutativityDFSRestarts:
			return mConditionalCommutativityDFSRestarts;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return CegarStatisticsType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { CegarLoopStatisticsDefinitions.OverallTime.toString(),
				CegarLoopStatisticsDefinitions.EmptinessCheckTime.toString(),
				CegarLoopStatisticsDefinitions.AutomataDifference.toString(),
				CegarLoopStatisticsDefinitions.DeadEndRemovalTime.toString(),
				CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString(),
				CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString(),
				CegarLoopStatisticsDefinitions.DumpTime.toString(),
				CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime.toString(),
				CegarLoopStatisticsDefinitions.ConditionalCommutativityCheckTime.toString()};
	}
}
