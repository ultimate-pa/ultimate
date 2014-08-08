package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType.SizeIterationPair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class CegarLoopBenchmarkGenerator extends BenchmarkGeneratorWithStopwatches implements IBenchmarkDataProvider {
	
	private final BenchmarkData m_EcData = new BenchmarkData();
	private final BenchmarkData m_TcData = new BenchmarkData();
	private final BenchmarkData m_TiData = new BenchmarkData();
	private int m_StatesRemovedByMinimization = 0;
	private int m_Iterations = 0;
	private SizeIterationPair m_BiggestAbstraction = CegarLoopBenchmarkType.getInstance().new SizeIterationPair(-1, -1);
	private BackwardCoveringInformation m_BCI = new BackwardCoveringInformation(0, 0);

	@Override
	public Collection<String> getKeys() {
		return getBenchmarkType().getKeys();
	}
	
	public void addEdgeCheckerData(IBenchmarkDataProvider ecbd) {
		m_EcData.aggregateBenchmarkData(ecbd);
	}
	
	public void addTraceCheckerData(IBenchmarkDataProvider tcbd) {
		m_TcData.aggregateBenchmarkData(tcbd);
	}
	
	public void addTotalInterpolationData(IBenchmarkDataProvider tibd) {
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
		if(size > m_BiggestAbstraction.getSize()) {
			m_BiggestAbstraction = CegarLoopBenchmarkType.getInstance().new SizeIterationPair(size, iteration);
		}
	}

	@Override
	public Object getValue(String key) {
		switch (key) {
		case CegarLoopBenchmarkType.s_OverallTime:
		case CegarLoopBenchmarkType.s_AutomataDifference:
		case CegarLoopBenchmarkType.s_DeadEndRemovalTime:
		case CegarLoopBenchmarkType.s_AutomataMinimizationTime:
		case CegarLoopBenchmarkType.s_HoareAnnotationTime:
		case CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime:
			try {
				return getElapsedTime(key);
			} catch (StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case CegarLoopBenchmarkType.s_EdgeCheckerData:
			return m_EcData;
		case CegarLoopBenchmarkType.s_TraceCheckerBenchmark:
			return m_TcData;
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
	public IBenchmarkType getBenchmarkType() {
		return CegarLoopBenchmarkType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { CegarLoopBenchmarkType.s_OverallTime, 
				CegarLoopBenchmarkType.s_AutomataDifference, 
				CegarLoopBenchmarkType.s_DeadEndRemovalTime, 
				CegarLoopBenchmarkType.s_AutomataMinimizationTime, 
				CegarLoopBenchmarkType.s_HoareAnnotationTime,
				CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime};
	}
	
	

}
