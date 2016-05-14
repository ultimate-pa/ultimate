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

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType.SizeIterationPair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

public class CegarLoopStatisticsGenerator extends StatisticsGeneratorWithStopwatches implements IStatisticsDataProvider {

	private Object m_Result;
	private final StatisticsData m_EcData = new StatisticsData();
	private final StatisticsData m_PuData = new StatisticsData();
	private final StatisticsData m_TcData = new StatisticsData();
	private final StatisticsData m_TiData = new StatisticsData();
	private final StatisticsData m_InterpolantConsolidationBenchmarks = new StatisticsData();
	private int m_StatesRemovedByMinimization = 0;
	private int m_Iterations = 0;
	private int m_AbsIntIterations = 0;
	private SizeIterationPair m_BiggestAbstraction = CegarStatisticsType.getInstance().new SizeIterationPair(-1, -1);
	private BackwardCoveringInformation m_BCI = new BackwardCoveringInformation(0, 0);
	private int m_AbsIntStrong = 0;
	private int m_TraceHistogramMaximum = 0;

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}

	public void setResult(Object result) {
		m_Result = result;
	}

	public void addEdgeCheckerData(IStatisticsDataProvider ecbd) {
		m_EcData.aggregateBenchmarkData(ecbd);
	}

	public void addPredicateUnifierData(IStatisticsDataProvider pubd) {
		m_PuData.aggregateBenchmarkData(pubd);
	}

	public void addTraceCheckerData(IStatisticsDataProvider tcbd) {
		m_TcData.aggregateBenchmarkData(tcbd);
	}

	public void addInterpolationConsolidationData(IStatisticsDataProvider tcbd) {
		m_InterpolantConsolidationBenchmarks.aggregateBenchmarkData(tcbd);
	}

	public void addTotalInterpolationData(IStatisticsDataProvider tibd) {
		m_TiData.aggregateBenchmarkData(tibd);
	}

	public void addBackwardCoveringInformation(BackwardCoveringInformation bci) {
		m_BCI = new BackwardCoveringInformation(m_BCI, bci);
	}

	public void announceStatesRemovedByMinimization(int statesRemoved) {
		m_StatesRemovedByMinimization += statesRemoved;
	}

	public void announceNextIteration() {
		m_Iterations++;
	}
	
	public void announceNextAbsIntIteration() {
		m_AbsIntIterations++;
	}
	
	public void announceStrongAbsInt() {
		m_AbsIntStrong++;
	}

	public void reportAbstractionSize(int size, int iteration) {
		if (size > m_BiggestAbstraction.getSize()) {
			m_BiggestAbstraction = CegarStatisticsType.getInstance().new SizeIterationPair(size, iteration);
		}
	}
	
	public void reportTraceHistogramMaximum(int maxCurrentTrace) {
		if (maxCurrentTrace > m_TraceHistogramMaximum) {
			m_TraceHistogramMaximum = maxCurrentTrace;
		}
	}

	@Override
	public Object getValue(String key) {
		final CegarLoopStatisticsDefinitions keyEnum = Enum.valueOf(CegarLoopStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case Result:
			return m_Result;
		case OverallTime:
		case AutomataDifference:
		case DeadEndRemovalTime:
		case AutomataMinimizationTime:
		case HoareAnnotationTime:
		case BasicInterpolantAutomatonTime:
		case AbstIntTime:
			try {
				return getElapsedTime(key);
			} catch (StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case HoareTripleCheckerStatistics:
			return m_EcData;
		case PredicateUnifierStatistics:
			return m_PuData;
		case TraceCheckerStatistics:
			return m_TcData;
		case InterpolantConsolidationStatistics:
			return m_InterpolantConsolidationBenchmarks;
		case TotalInterpolationStatistics:
			return m_TiData;
		case StatesRemovedByMinimization:
			return m_StatesRemovedByMinimization;
		case OverallIterations:
			return m_Iterations;
		case TraceHistogramMax:
			return m_TraceHistogramMaximum;
		case AbstIntIterations:
			return m_AbsIntIterations;
		case AbstIntStrong:
			return m_AbsIntStrong;			
		case BiggestAbstraction:
			return m_BiggestAbstraction;
		case InterpolantCoveringCapability:
			return m_BCI;
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
				CegarLoopStatisticsDefinitions.AbstIntTime.toString(),
				CegarLoopStatisticsDefinitions.AutomataDifference.toString(), 
				CegarLoopStatisticsDefinitions.DeadEndRemovalTime.toString(),
				CegarLoopStatisticsDefinitions.AutomataMinimizationTime.toString(), 
				CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString(),
				CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString() };
	}


}
