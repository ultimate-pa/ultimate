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

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType.SizeIterationPair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.StatisticsData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IStatisticsType;

public class CegarLoopBenchmarkGenerator extends StatisticsGeneratorWithStopwatches implements IStatisticsDataProvider {

	private Object m_Result;
	private final StatisticsData m_EcData = new StatisticsData();
	private final StatisticsData m_PuData = new StatisticsData();
	private final StatisticsData m_TcData = new StatisticsData();
	private final StatisticsData m_TiData = new StatisticsData();
	private final StatisticsData m_InterpolantConsolidationBenchmarks = new StatisticsData();
	private int m_StatesRemovedByMinimization = 0;
	private int m_Iterations = 0;
	private SizeIterationPair m_BiggestAbstraction = CegarLoopBenchmarkType.getInstance().new SizeIterationPair(-1, -1);
	private BackwardCoveringInformation m_BCI = new BackwardCoveringInformation(0, 0);

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

	public void reportAbstractionSize(int size, int iteration) {
		if (size > m_BiggestAbstraction.getSize()) {
			m_BiggestAbstraction = CegarLoopBenchmarkType.getInstance().new SizeIterationPair(size, iteration);
		}
	}

	@Override
	public Object getValue(String key) {
		switch (key) {
		case CegarLoopBenchmarkType.s_Result:
			return m_Result;
		case CegarLoopBenchmarkType.s_OverallTime:
		case CegarLoopBenchmarkType.s_AutomataDifference:
		case CegarLoopBenchmarkType.s_DeadEndRemovalTime:
		case CegarLoopBenchmarkType.s_AutomataMinimizationTime:
		case CegarLoopBenchmarkType.s_HoareAnnotationTime:
		case CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime:
		case CegarLoopBenchmarkType.s_AbsIntTime:
			try {
				return getElapsedTime(key);
			} catch (StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case CegarLoopBenchmarkType.s_EdgeCheckerData:
			return m_EcData;
		case CegarLoopBenchmarkType.s_PredicateUnifierData:
			return m_PuData;
		case CegarLoopBenchmarkType.s_TraceCheckerBenchmark:
			return m_TcData;
		case CegarLoopBenchmarkType.s_InterpolantConsolidationBenchmark:
			return m_InterpolantConsolidationBenchmarks;
		case CegarLoopBenchmarkType.s_TotalInterpolationBenchmark:
			return m_TiData;
		case CegarLoopBenchmarkType.s_StatesRemovedByMinimization:
			return m_StatesRemovedByMinimization;
		case CegarLoopBenchmarkType.s_OverallIterations:
			return m_Iterations;
		case CegarLoopBenchmarkType.s_BiggestAbstraction:
			return m_BiggestAbstraction;
		case CegarLoopBenchmarkType.s_InterpolantCoveringCapability:
			return m_BCI;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return CegarLoopBenchmarkType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { CegarLoopBenchmarkType.s_OverallTime, CegarLoopBenchmarkType.s_AbsIntTime,
				CegarLoopBenchmarkType.s_AutomataDifference, CegarLoopBenchmarkType.s_DeadEndRemovalTime,
				CegarLoopBenchmarkType.s_AutomataMinimizationTime, CegarLoopBenchmarkType.s_HoareAnnotationTime,
				CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime };
	}
}
