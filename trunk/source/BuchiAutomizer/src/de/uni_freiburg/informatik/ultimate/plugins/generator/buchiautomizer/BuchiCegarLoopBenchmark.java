package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkType;

public class BuchiCegarLoopBenchmark extends CegarLoopBenchmarkType implements IBenchmarkType {
	
	private static final BuchiCegarLoopBenchmark s_Instance = new BuchiCegarLoopBenchmark();
	
	public static final String s_NonLiveStateRemoval = "NonLiveStateRemoval";
	public static final String s_BuchiClosure = "BuchiClosure";
	public static final String s_NontrivialModuleStages = "NontrivialModuleStages";
	public static final String s_LassoAnalysisTime = "LassoAnalysisTime";
	public static final String s_LassoAnalysisResults = "LassoAnalysisResults";
	
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
		return keyList;
	}
	
	@Override
	public Object aggregate(String key, Object value1, Object value2) {
		switch (key) {
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
		default:
			break;
		}
		return super.aggregate(key, value1, value2);
	}

	@Override
	public String prettyprintBenchmarkData(BenchmarkData benchmarkData) {
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
	
	public static class LassoAnalysisResults {
		public int m_LassoNonterminating;
		public int m_TerminationUnknown;
		/**
		 * Cases where (already a single iteration of) the loop is infeasible.
		 */
		public int m_StemFeasibleLoopInfeasible;
		/**
		 * Cases where the stem is feasible, (a single iteration of) the loop 
		 * is feasible but the loop is terminating.
		 */
		public int m_StemFeasibleLoopTerminating;
		/**
		 * Cases where stem and loop are feasible but the concatenation of stem
		 * and loop is infeasible.
		 */
		public int m_ConcatenationInfeasible;
		/**
		 * Cases where stem and loop are feasible but the concatenation of stem
		 * and loop is infeasible and the loop is terminating.
		 */
		public int m_ConcatInfeasibleLoopTerminating;
		/**
		 * Cases where the stem is infeasible and the loop is nonterminating.
		 */
		public int m_StemInfeasibleLoopNonterminating;
		/**
		 * Cases where the stem is infeasible and the termination/feasibility
		 * of the loop is unknown.
		 */
		public int m_StemInfeasibleLoopUnknown;
		/**
		 * Cases where the stem is infeasible and the loop is infeasible.
		 */
		public int m_StemInfeasibleLoopInfeasible;
		/**
		 * Cases where both, stem and loop are infeasible.
		 */
		public int m_StemInfeasibleLoopTerminating;
		/**
		 * Cases where the stem and the loop are feasible, the loop itself is
		 * nonterminating but the lasso is terminating.
		 */
		public int m_LassoTerminating;
		
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("nont " + m_LassoNonterminating);
			sb.append(", unkn " + m_TerminationUnknown);
			sb.append(", SFLI " + m_StemFeasibleLoopInfeasible);
			sb.append(", SFLT " + m_StemFeasibleLoopTerminating);
			sb.append(", conc " + m_ConcatenationInfeasible);
			sb.append(", concLT " + m_ConcatInfeasibleLoopTerminating);
			sb.append(", lasso " + m_LassoTerminating);
			sb.append(", SILU " + m_StemInfeasibleLoopUnknown);
			sb.append(", SILI " + m_StemInfeasibleLoopInfeasible);
			sb.append(", SILT " + m_StemInfeasibleLoopTerminating);
			sb.append(".");
			return sb.toString();
		}
		
		public void aggregate(LassoAnalysisResults lassoAnalysisResults) {
			m_LassoNonterminating = lassoAnalysisResults.m_LassoNonterminating;
			m_TerminationUnknown = lassoAnalysisResults.m_TerminationUnknown;
			m_StemFeasibleLoopInfeasible = lassoAnalysisResults.m_StemFeasibleLoopInfeasible;
			m_StemFeasibleLoopTerminating = lassoAnalysisResults.m_StemFeasibleLoopTerminating;
			m_ConcatenationInfeasible = lassoAnalysisResults.m_ConcatenationInfeasible;
			m_ConcatInfeasibleLoopTerminating = lassoAnalysisResults.m_ConcatInfeasibleLoopTerminating;
			m_StemInfeasibleLoopNonterminating = lassoAnalysisResults.m_StemInfeasibleLoopNonterminating;
			m_StemInfeasibleLoopUnknown = lassoAnalysisResults.m_StemInfeasibleLoopUnknown;
			m_StemInfeasibleLoopInfeasible = lassoAnalysisResults.m_StemInfeasibleLoopInfeasible;
			m_StemInfeasibleLoopTerminating = lassoAnalysisResults.m_StemInfeasibleLoopTerminating;
			m_LassoTerminating = lassoAnalysisResults.m_LassoTerminating;
		}
	}

}
