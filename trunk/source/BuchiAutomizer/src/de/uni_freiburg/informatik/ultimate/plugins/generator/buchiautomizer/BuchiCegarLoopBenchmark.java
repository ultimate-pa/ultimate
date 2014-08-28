package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.swing.text.html.parser.Entity;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkType;

public class BuchiCegarLoopBenchmark extends CegarLoopBenchmarkType implements IBenchmarkType {
	
	private static final BuchiCegarLoopBenchmark s_Instance = new BuchiCegarLoopBenchmark();
	
	public static final String s_NonLiveStateRemoval = "NonLiveStateRemoval";
	public static final String s_BuchiClosure = "BuchiClosure";
	public static final String s_NontrivialModuleStages = "NontrivialModuleStages";
	public static final String s_LassoAnalysisTime = "LassoAnalysisTime";
	public static final String s_LassoAnalysisResults = "LassoAnalysisResults";
	public static final String s_InterpolantCoveringCapabilityFinite = "InterpolantCoveringCapabilityFinite";
	public static final String s_InterpolantCoveringCapabilityBuchi = "InterpolantCoveringCapabilityBuchi";
	
	public static BuchiCegarLoopBenchmark getInstance() {
		return s_Instance;
	}

	@Override
	public Collection<String> getKeys() {
		ArrayList<String> keyList = new ArrayList<String>(super.getKeys());
		keyList.add(s_NonLiveStateRemoval);
		keyList.add(s_BuchiClosure);
		keyList.add(s_NontrivialModuleStages);
		keyList.add(s_LassoAnalysisTime);
		keyList.add(s_LassoAnalysisResults);
		keyList.add(s_InterpolantCoveringCapabilityFinite);
		keyList.add(s_InterpolantCoveringCapabilityBuchi);
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
			if (results.contains(Result.NONTERMINATING)) {
				return Result.NONTERMINATING;
			} else if (results.contains(Result.UNKNOWN)) {
				return Result.UNKNOWN;
			} else if (results.contains(Result.TIMEOUT)) {
				return Result.TIMEOUT;
			} else if (results.contains(Result.TERMINATING)) {
				return Result.TERMINATING;
			} else {
				throw new AssertionError();
			}
		case s_NontrivialModuleStages:
		{
			int[] array1 = (int[]) value1;
			int[] array2 = (int[]) value2;
			assert array1.length == 4;
			assert array2.length == 4;
			int[] result = new int[4];
			for (int i=0; i<4; i++) {
				result[i] = array1[i] + array1[i];
			}
			return result;
		}
		case s_InterpolantCoveringCapabilityFinite:
		case s_InterpolantCoveringCapabilityBuchi:
			BackwardCoveringInformation bci1 = (BackwardCoveringInformation) value1;
			BackwardCoveringInformation bci2 = (BackwardCoveringInformation) value2;
			return new BackwardCoveringInformation(bci1, bci2);
		default:
			return super.aggregate(key, value1, value2);
		}
	}

	@Override
	public String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("BüchiAutomizer plugin needed ");
		Long overallTime = (Long) benchmarkData.getValue(s_OverallTime);
		sb.append(prettyprintNanoseconds(overallTime));
		sb.append(" and ");
		Integer overallIterations = (Integer) benchmarkData.getValue(s_OverallIterations);
		sb.append(overallIterations);
		sb.append(" iterations. ");
		
		Long laTime = (Long) benchmarkData.getValue(s_LassoAnalysisTime);
		sb.append("Analysis of lassos took ");
		sb.append(prettyprintNanoseconds(laTime));
		sb.append(". ");
		
		BenchmarkData ecData = 
				(BenchmarkData) benchmarkData.getValue(s_EdgeCheckerData);
		Long ecTime;
		if (ecData.getBenchmarkType() == null) {
			ecTime = 0L;
		} else {
			ecTime = (Long) ecData.getValue(EdgeCheckerBenchmarkType.s_EdgeCheckerTime);
		}
		
		sb.append("Construction of modules took ");
		sb.append(prettyprintNanoseconds(ecTime));
		Long differenceTime = (Long) benchmarkData.getValue(s_AutomataDifference);
		sb.append(". ");
		sb.append("Büchi inclusion checks took ");
		sb.append(prettyprintNanoseconds(differenceTime - ecTime));
		sb.append(". ");
		
		sb.append("Minimization removed ");
		sb.append(benchmarkData.getValue(s_StatesRemovedByMinimization));
		sb.append(" states and took ");
		Long time = (Long) benchmarkData.getValue(s_AutomataMinimizationTime);
		sb.append(prettyprintNanoseconds(time));
		sb.append(". ");
		
		sb.append("Non-live state removal took ");
		Long nonLiveTime = (Long) benchmarkData.getValue(s_NonLiveStateRemoval);
		sb.append(prettyprintNanoseconds(nonLiveTime));
		sb.append(" Buchi closure took ");
		Long buchiClosureTime = (Long) benchmarkData.getValue(s_BuchiClosure);
		sb.append(prettyprintNanoseconds(buchiClosureTime));
		sb.append(". ");
		
		SizeIterationPair sip = (SizeIterationPair) benchmarkData.getValue(s_BiggestAbstraction);
		sb.append("Biggest automaton had ");
		sb.append(sip.getSize());
		sb.append(" states and ocurred in iteration ");
		sb.append(sip.getIteration());
		sb.append(".\t");
		
		int[] stages = (int[]) benchmarkData.getValue(s_NontrivialModuleStages);
		sb.append("Nontrivial modules had stage ");
		sb.append(Arrays.toString(stages));
		sb.append(".\t");
		
		BackwardCoveringInformation bcif = (BackwardCoveringInformation) benchmarkData.getValue(s_InterpolantCoveringCapabilityFinite);
		sb.append(s_InterpolantCoveringCapabilityFinite);
		sb.append(": ");
		sb.append(bcif.toString());
		sb.append("\t");
		
		BackwardCoveringInformation bcib = (BackwardCoveringInformation) benchmarkData.getValue(s_InterpolantCoveringCapabilityBuchi);
		sb.append(s_InterpolantCoveringCapabilityBuchi);
		sb.append(": ");
		sb.append(bcib.toString());
		sb.append("\t");
		
		sb.append(s_EdgeCheckerData);
		sb.append(": ");
		sb.append(ecData);
		sb.append("\t");
		
		sb.append(s_LassoAnalysisResults);
		sb.append(": ");
		LassoAnalysisResults lar = 
				(LassoAnalysisResults) benchmarkData.getValue(s_LassoAnalysisResults);
		sb.append(lar.toString());
		return sb.toString();
	}
	
	public static class LassoAnalysisResults implements IBenchmarkDataProvider, IBenchmarkType {
		public static final String s_LassoNonterminating = "nont";
		public static final String s_TerminationUnknown = "unkn";
		/**
		 * Cases where (already a single iteration of) the loop is infeasible.
		 */
		public static final String s_StemFeasibleLoopInfeasible = "SFLI";
		/**
		 * Cases where the stem is feasible, (a single iteration of) the loop 
		 * is feasible but the loop is terminating.
		 */
		public static final String s_StemFeasibleLoopTerminating = "SFLT";
		/**
		 * Cases where stem and loop are feasible but the concatenation of stem
		 * and loop is infeasible.
		 */
		public static final String s_ConcatenationInfeasible = "conc";
		/**
		 * Cases where stem and loop are feasible but the concatenation of stem
		 * and loop is infeasible and the loop is terminating.
		 */
		public static final String s_ConcatInfeasibleLoopTerminating = "concLT";
		/**
		 * Cases where the stem is infeasible and the loop is nonterminating.
		 */
		public static final String s_StemInfeasibleLoopNonterminating = "SILN";
		/**
		 * Cases where the stem is infeasible and the termination/feasibility
		 * of the loop is unknown.
		 */
		public static final String s_StemInfeasibleLoopUnknown = "SILU";
		/**
		 * Cases where the stem is infeasible and the loop is infeasible.
		 */
		public static final String s_StemInfeasibleLoopInfeasible = "SILI";
		/**
		 * Cases where both, stem and loop are infeasible.
		 */
		public static final String s_StemInfeasibleLoopTerminating = "SILT";
		/**
		 * Cases where the stem and the loop are feasible, the loop itself is
		 * nonterminating but the lasso is terminating.
		 */
		public static final String s_LassoTerminating = "lasso";
		
		public final Map<String, Integer> m_Map;
		
		public LassoAnalysisResults() {
			m_Map = new LinkedHashMap<String, Integer>();
			m_Map.put(s_LassoNonterminating, 0);
			m_Map.put(s_TerminationUnknown, 0);
			m_Map.put(s_StemFeasibleLoopInfeasible, 0);
			m_Map.put(s_StemFeasibleLoopTerminating, 0);
			m_Map.put(s_ConcatenationInfeasible, 0);
			m_Map.put(s_ConcatInfeasibleLoopTerminating, 0);
			m_Map.put(s_StemInfeasibleLoopNonterminating, 0);
			m_Map.put(s_StemInfeasibleLoopUnknown, 0);
			m_Map.put(s_StemInfeasibleLoopInfeasible, 0);
			m_Map.put(s_StemInfeasibleLoopTerminating, 0);
			m_Map.put(s_LassoTerminating, 0);
		}
		
		
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (String key : getKeys()) {
				sb.append(key);
				sb.append(getValue(key));
				sb.append(" ");
			}
			return sb.toString();
		}
		

		public void increment(String key) {
			int value = m_Map.get(key);
			m_Map.put(key, value + 1);
		}
		
//		public void aggregate(LassoAnalysisResults lassoAnalysisResults) {
//			m_LassoNonterminating = lassoAnalysisResults.m_LassoNonterminating;
//			m_TerminationUnknown = lassoAnalysisResults.m_TerminationUnknown;
//			m_StemFeasibleLoopInfeasible = lassoAnalysisResults.m_StemFeasibleLoopInfeasible;
//			m_StemFeasibleLoopTerminating = lassoAnalysisResults.m_StemFeasibleLoopTerminating;
//			m_ConcatenationInfeasible = lassoAnalysisResults.m_ConcatenationInfeasible;
//			m_ConcatInfeasibleLoopTerminating = lassoAnalysisResults.m_ConcatInfeasibleLoopTerminating;
//			m_StemInfeasibleLoopNonterminating = lassoAnalysisResults.m_StemInfeasibleLoopNonterminating;
//			m_StemInfeasibleLoopUnknown = lassoAnalysisResults.m_StemInfeasibleLoopUnknown;
//			m_StemInfeasibleLoopInfeasible = lassoAnalysisResults.m_StemInfeasibleLoopInfeasible;
//			m_StemInfeasibleLoopTerminating = lassoAnalysisResults.m_StemInfeasibleLoopTerminating;
//			m_LassoTerminating = lassoAnalysisResults.m_LassoTerminating;
//		}

		@Override
		public Collection<String> getKeys() {
			return m_Map.keySet();
		}

		@Override
		public Object getValue(String key) {
			return m_Map.get(key);
		}

		@Override
		public IBenchmarkType getBenchmarkType() {
			return this;
		}

		@Override
		public Object aggregate(String key, Object value1, Object value2) {
			throw new AssertionError("not yet implemented");
		}

		@Override
		public String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData) {
			LassoAnalysisResults lar = (LassoAnalysisResults) benchmarkData;
			StringBuilder sb = new StringBuilder();
			for (String key : lar.getKeys()) {
				sb.append(key);
				sb.append(lar.getValue(key));
				sb.append(" ");
			}
			return sb.toString();
		}


	}

}
