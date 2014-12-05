package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class CegarLoopBenchmarkType implements IBenchmarkType {
	
	public static final String s_Result = "Result";
	public static final String s_OverallTime = "Overall time";
	public static final String s_OverallIterations = "Overall iterations";
	public static final String s_AutomataDifference = "Automata difference";
	public static final String s_DeadEndRemovalTime = "Dead end removal time";
	public static final String s_AutomataMinimizationTime = "Minimization time";
	public static final String s_HoareAnnotationTime = "Time for computing Hoare annotation";
	public static final String s_EdgeCheckerData = "EdgeCheckerBenchmarkData";
	public static final String s_StatesRemovedByMinimization = "States removed by minization";
	public static final String s_BasicInterpolantAutomatonTime = "BasicInterpolantAutomatonTime";
	public static final String s_BiggestAbstraction = "BiggestAbstraction";
	public static final String s_TraceCheckerBenchmark = "TraceCheckerBenchmark";
	public static final String s_InterpolantCoveringCapability = "InterpolantCoveringCapability";
	public static final String s_TotalInterpolationBenchmark = "TotalInterpolationBenchmark";
	
	private static final CegarLoopBenchmarkType s_Instance = new CegarLoopBenchmarkType();
	
	public static CegarLoopBenchmarkType getInstance() {
		return s_Instance;
	}

	@Override
	public Collection<String> getKeys() {
		ArrayList<String> keyList = new ArrayList<String>();
		keyList.addAll(Arrays.asList(new String[] { 
				s_Result, s_OverallTime, s_OverallIterations, 
				s_AutomataDifference, 
				s_DeadEndRemovalTime, 
				s_AutomataMinimizationTime, s_HoareAnnotationTime, 
				s_BasicInterpolantAutomatonTime, s_BiggestAbstraction }));
		keyList.add(s_EdgeCheckerData);
		keyList.add(s_StatesRemovedByMinimization);
		keyList.add(s_TraceCheckerBenchmark);
		keyList.add(s_InterpolantCoveringCapability);
		keyList.add(s_TotalInterpolationBenchmark);
		return keyList;
	}
	
	@Override
	public Object aggregate(String key, Object value1, Object value2) {
		switch (key) {
		case s_Result:
			Result result1 = (Result) value1;
			Result result2 = (Result) value2;
			Set<Result> results = new HashSet<Result>();
			results.add(result1);
			results.add(result2);
			if (results.contains(Result.UNSAFE)) {
				return Result.UNSAFE;
			} else if (results.contains(Result.UNKNOWN)) {
				return Result.UNKNOWN;
			} else if (results.contains(Result.TIMEOUT)) {
				return Result.TIMEOUT;
			} else if (results.contains(Result.SAFE)) {
				return Result.SAFE;
			} else {
				throw new AssertionError();
			}
		case s_OverallTime:
		case s_AutomataDifference:
		case s_DeadEndRemovalTime:
		case s_AutomataMinimizationTime:
		case s_HoareAnnotationTime:
		case s_BasicInterpolantAutomatonTime:
			Long time1 = (Long) value1;
			Long time2 = (Long) value2;
			return time1 + time2;
		case s_EdgeCheckerData:
		case s_TraceCheckerBenchmark:
		case s_TotalInterpolationBenchmark:
			BenchmarkData bmData1 = (BenchmarkData) value1;
			BenchmarkData bmData2 = (BenchmarkData) value2;
			if (bmData2.getBenchmarkType() == null) {
				// benchmark not provided for this CEGAR loop,
				// add nothing
			} else {
				bmData1.aggregateBenchmarkData(bmData2);
			}
			return bmData1;
		case s_StatesRemovedByMinimization:
		case s_OverallIterations:
			Integer number1 = (Integer) value1;
			Integer number2 = (Integer) value2;
			return number1 + number2;
		case s_BiggestAbstraction:
			SizeIterationPair sip1 = (SizeIterationPair) value1;
			SizeIterationPair sip2 = (SizeIterationPair) value2;
			if (sip1.getSize() >= sip2.getSize()) {
				return sip1;
			} else {
				return sip2;
			}
		case s_InterpolantCoveringCapability:
			BackwardCoveringInformation bci1 = (BackwardCoveringInformation) value1;
			BackwardCoveringInformation bci2 = (BackwardCoveringInformation) value2;
			return new BackwardCoveringInformation(bci1, bci2);
		default:
			throw new AssertionError();
		}
	}

	@Override
	public String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("Automizer needed ");
		Long overallTime = (Long) benchmarkData.getValue(s_OverallTime);
		sb.append(prettyprintNanoseconds(overallTime));
		sb.append(" and ");
		Integer overallIterations = (Integer) benchmarkData.getValue(s_OverallIterations);
		sb.append(overallIterations);
		sb.append(" iterations. ");
		
		sb.append("Automata difference (including EdgeChecker) took ");
		Long differenceTime = (Long) benchmarkData.getValue(s_AutomataDifference);
		sb.append(prettyprintNanoseconds(differenceTime));
		sb.append(". ");
		
		sb.append("Computation of Hoare annotation took ");
		Long hoareTime = (Long) benchmarkData.getValue(s_HoareAnnotationTime);
		sb.append(prettyprintNanoseconds(hoareTime));
		sb.append(". ");
		
		sb.append("Minimization removed ");
		sb.append(benchmarkData.getValue(s_StatesRemovedByMinimization));
		sb.append(" states and took ");
		Long time = (Long) benchmarkData.getValue(s_AutomataMinimizationTime);
		sb.append(prettyprintNanoseconds(time));
		sb.append(". ");
		
		SizeIterationPair sip = (SizeIterationPair) benchmarkData.getValue(s_BiggestAbstraction);
		sb.append("Biggest automaton had ");
		sb.append(sip.getSize());
		sb.append(" states and ocurred in iteration ");
		sb.append(sip.getIteration());
		sb.append(".\t");
		
		BackwardCoveringInformation bci = (BackwardCoveringInformation) benchmarkData.getValue(s_InterpolantCoveringCapability);
		sb.append(s_InterpolantCoveringCapability);
		sb.append(": ");
		sb.append(bci.toString());
		sb.append("\t");

		sb.append("ICC %");
		sb.append(": ");
		sb.append(new Double(((double) bci.getSuccessfullBackwardCoverings())
				/bci.getPotentialBackwardCoverings()).toString());
		sb.append("\t");
		
		sb.append(s_EdgeCheckerData);
		sb.append(": ");
		BenchmarkData ecData = 
				(BenchmarkData) benchmarkData.getValue(s_EdgeCheckerData);
		sb.append(ecData);
		sb.append("\t");
		
		sb.append(s_TraceCheckerBenchmark);
		sb.append(": ");
		BenchmarkData tcData = 
				(BenchmarkData) benchmarkData.getValue(s_TraceCheckerBenchmark);
		sb.append(tcData);
		sb.append("\t");
		
		BenchmarkData tiData = 
				(BenchmarkData) benchmarkData.getValue(s_TotalInterpolationBenchmark);
		if (!tiData.isEmpty()) {
			sb.append(s_TotalInterpolationBenchmark);
			sb.append(": ");
			sb.append(tiData);
		}
		
		
		return sb.toString();
	}
	
	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

	public class SizeIterationPair {
		final int m_Size;
		final int m_Iteration;
		public SizeIterationPair(int size, int iteration) {
			super();
			m_Size = size;
			m_Iteration = iteration;
		}
		public int getSize() {
			return m_Size;
		}
		public int getIteration() {
			return m_Iteration;
		}
		@Override
		public String toString() {
			return "size=" + m_Size + "occurred in iteration="
					+ m_Iteration;
		}
		
		
		
		
	}

}
