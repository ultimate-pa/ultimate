/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class BuchiCegarLoopBenchmark extends CegarStatisticsType implements IStatisticsType {
	
	private static final BuchiCegarLoopBenchmark s_Instance = new BuchiCegarLoopBenchmark();
	
	public static final String s_Result = "Result";
	public static final String s_HighestRank = "HighestRank";
	public static final String s_NonLiveStateRemoval = "NonLiveStateRemoval";
	public static final String s_BuchiClosure = "BuchiClosure";
	public static final String s_NontrivialModuleStages = "NontrivialModuleStages";
	public static final String s_LassoAnalysisTime = "LassoAnalysisTime";
	public static final String s_LassoAnalysisResults = "LassoAnalysisResults";
	public static final String s_InterpolantCoveringCapabilityFinite = "InterpolantCoveringCapabilityFinite";
	public static final String s_InterpolantCoveringCapabilityBuchi = "InterpolantCoveringCapabilityBuchi";
	public static final String s_LassoPreprocessingBenchmarks = "LassoPreprocessingBenchmarks";
	public static final String s_LassoTerminationAnalysisBenchmarks = "LassoTerminationAnalysisBenchmarks";
	public static final String s_LassoNonterminationAnalysisBenchmarks = "LassoNonterminationAnalysisBenchmarks";
	public static final String s_LassoNonterminationAnalysisSATFixpoint = "LassoNonterminationAnalysisSatFixpoint";
	public static final String s_LassoNonterminationAnalysisSATUnbounded = "LassoNonterminationAnalysisSatUnbounded";
	public static final String s_LassoNonterminationAnalysisUNSAT = "LassoNonterminationAnalysisUnsat";
	public static final String s_LassoNonterminationAnalysisUNKNOWN = "LassoNonterminationAnalysisUnknown";
	public static final String s_LassoNonterminationAnalysisTIME = "LassoNonterminationAnalysisTime";
	public static final String s_MinimizationsOfDetermnisticAutomatomata = "MinimizationsOfDetermnisticAutomatomata";
	public static final String s_MinimizationsOfNondetermnisticAutomatomata = "MinimizationsOfNondetermnisticAutomatomata";
	
	public static BuchiCegarLoopBenchmark getInstance() {
		return s_Instance;
	}

	@Override
	public Collection<String> getKeys() {
		final ArrayList<String> keyList = new ArrayList<String>(super.getKeys());
		keyList.add(s_HighestRank);
		keyList.add(s_NonLiveStateRemoval);
		keyList.add(s_BuchiClosure);
		keyList.add(s_NontrivialModuleStages);
		keyList.add(s_LassoAnalysisTime);
		keyList.add(s_LassoAnalysisResults);
		keyList.add(s_InterpolantCoveringCapabilityFinite);
		keyList.add(s_InterpolantCoveringCapabilityBuchi);
		keyList.add(s_LassoPreprocessingBenchmarks);
		keyList.add(s_LassoTerminationAnalysisBenchmarks);
		keyList.add(s_LassoNonterminationAnalysisSATFixpoint);
		keyList.add(s_LassoNonterminationAnalysisSATUnbounded);
		keyList.add(s_LassoNonterminationAnalysisUNSAT);
		keyList.add(s_LassoNonterminationAnalysisUNKNOWN);
		keyList.add(s_LassoNonterminationAnalysisTIME);
		keyList.add(s_MinimizationsOfDetermnisticAutomatomata);
		keyList.add(s_MinimizationsOfNondetermnisticAutomatomata);
		return keyList;
	}
	
	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		switch (key) {
		case s_Result:
			final Result result1 = (Result) value1;
			final Result result2 = (Result) value2;
			final Set<Result> results = new HashSet<Result>();
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
			final int[] array1 = (int[]) value1;
			final int[] array2 = (int[]) value2;
			assert array1.length == 4;
			assert array2.length == 4;
			final int[] result = new int[4];
			for (int i=0; i<4; i++) {
				result[i] = array1[i] + array1[i];
			}
			return result;
		}
		case s_InterpolantCoveringCapabilityFinite:
		case s_InterpolantCoveringCapabilityBuchi:
			final BackwardCoveringInformation bci1 = (BackwardCoveringInformation) value1;
			final BackwardCoveringInformation bci2 = (BackwardCoveringInformation) value2;
			return new BackwardCoveringInformation(bci1, bci2);
		case s_LassoPreprocessingBenchmarks:
		case s_LassoTerminationAnalysisBenchmarks:
		case s_HighestRank:
		case s_LassoNonterminationAnalysisSATFixpoint:
		case s_LassoNonterminationAnalysisSATUnbounded:
		case s_LassoNonterminationAnalysisUNSAT:
		case s_LassoNonterminationAnalysisUNKNOWN:
		case s_LassoNonterminationAnalysisTIME:
			throw new AssertionError("not yet implemented");
		default:
			return super.aggregate(key, value1, value2);
		}
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		final StringBuilder sb = new StringBuilder();
		
		sb.append("BüchiAutomizer plugin needed ");
		final Long overallTime = (Long) benchmarkData.getValue(CegarLoopStatisticsDefinitions.OverallTime.toString());
		sb.append(prettyprintNanoseconds(overallTime));
		sb.append(" and ");
		final Integer overallIterations = (Integer) benchmarkData.getValue(CegarLoopStatisticsDefinitions.OverallIterations.toString());
		sb.append(overallIterations);
		sb.append(" iterations. ");
		
		sb.append(" TraceHistogramMax:");
		final Integer trMax = (Integer) benchmarkData.getValue(CegarLoopStatisticsDefinitions.TraceHistogramMax.toString());
		sb.append(trMax);
		sb.append(". ");
		
		final Long laTime = (Long) benchmarkData.getValue(s_LassoAnalysisTime);
		sb.append("Analysis of lassos took ");
		sb.append(prettyprintNanoseconds(laTime));
		sb.append(". ");
		
		final StatisticsData ecData =
				(StatisticsData) benchmarkData.getValue(CegarLoopStatisticsDefinitions.HoareTripleCheckerStatistics.toString());
		Long ecTime;
		if (ecData.getBenchmarkType() == null) {
			ecTime = 0L;
		} else {
			ecTime = (Long) ecData.getValue(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time));
		}
		
		sb.append("Construction of modules took ");
		sb.append(prettyprintNanoseconds(ecTime));
		final Long differenceTime = (Long) benchmarkData.getValue(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		sb.append(". ");
		sb.append("Büchi inclusion checks took ");
		sb.append(prettyprintNanoseconds(differenceTime - ecTime));
		sb.append(". ");
		
		sb.append("Highest rank in rank-based complementation ");
		final Integer highestRank = (Integer) benchmarkData.getValue(s_HighestRank);
		sb.append(highestRank);
		sb.append(". ");
		
		sb.append("Minimization of det autom ");
		sb.append(benchmarkData.getValue(s_MinimizationsOfDetermnisticAutomatomata.toString()));
		sb.append(". ");
		
		sb.append("Minimization of nondet autom ");
		sb.append(benchmarkData.getValue(s_MinimizationsOfNondetermnisticAutomatomata.toString()));
		sb.append(". ");
		
		sb.append("Automata minimization ");
		sb.append(benchmarkData.getValue(CegarLoopStatisticsDefinitions.AutomataMinimizationStatistics.toString()));
		sb.append(". ");
		
	
		sb.append("Non-live state removal took ");
		final Long nonLiveTime = (Long) benchmarkData.getValue(s_NonLiveStateRemoval);
		sb.append(prettyprintNanoseconds(nonLiveTime));
		sb.append(" Buchi closure took ");
		final Long buchiClosureTime = (Long) benchmarkData.getValue(s_BuchiClosure);
		sb.append(prettyprintNanoseconds(buchiClosureTime));
		sb.append(". ");
		
		final SizeIterationPair sip = (SizeIterationPair) benchmarkData.getValue(CegarLoopStatisticsDefinitions.BiggestAbstraction.toString());
		sb.append("Biggest automaton had ");
		sb.append(sip.getSize());
		sb.append(" states and ocurred in iteration ");
		sb.append(sip.getIteration());
		sb.append(".\t");
		
		final int[] stages = (int[]) benchmarkData.getValue(s_NontrivialModuleStages);
		sb.append("Nontrivial modules had stage ");
		sb.append(Arrays.toString(stages));
		sb.append(".\t");
		
		final BackwardCoveringInformation bcif = (BackwardCoveringInformation) benchmarkData.getValue(s_InterpolantCoveringCapabilityFinite);
		sb.append(s_InterpolantCoveringCapabilityFinite);
		sb.append(": ");
		sb.append(bcif.toString());
		sb.append("\t");
		
		final BackwardCoveringInformation bcib = (BackwardCoveringInformation) benchmarkData.getValue(s_InterpolantCoveringCapabilityBuchi);
		sb.append(s_InterpolantCoveringCapabilityBuchi);
		sb.append(": ");
		sb.append(bcib.toString());
		sb.append("\t");
		
		sb.append(CegarLoopStatisticsDefinitions.HoareTripleCheckerStatistics.toString());
		sb.append(": ");
		sb.append(ecData);
		sb.append("\t");
		
		sb.append(s_LassoAnalysisResults);
		sb.append(": ");
		final LassoAnalysisResults lar =
				(LassoAnalysisResults) benchmarkData.getValue(s_LassoAnalysisResults);
		sb.append(lar.toString());
		
		sb.append(s_LassoPreprocessingBenchmarks);
		sb.append(": ");
		final List<PreprocessingBenchmark> ppbench = (List<PreprocessingBenchmark>) benchmarkData.getValue(s_LassoPreprocessingBenchmarks);
		sb.append(PreprocessingBenchmark.prettyprint(ppbench));
		sb.append(s_LassoTerminationAnalysisBenchmarks);
		sb.append(": ");
		final List<TerminationAnalysisBenchmark> tabbench = (List<TerminationAnalysisBenchmark>) benchmarkData.getValue(s_LassoTerminationAnalysisBenchmarks);
		sb.append(prettyPrintTerminationAnalysisBenchmark(tabbench));
		sb.append(s_LassoTerminationAnalysisBenchmarks);
		sb.append(": ");

		sb.append(s_LassoNonterminationAnalysisSATFixpoint);
		sb.append(": ");
		sb.append(benchmarkData.getValue(s_LassoNonterminationAnalysisSATFixpoint));
		sb.append("\t");

		
		sb.append(s_LassoNonterminationAnalysisSATUnbounded);
		sb.append(": ");
		sb.append(benchmarkData.getValue(s_LassoNonterminationAnalysisSATUnbounded));
		sb.append("\t");
		
		sb.append(s_LassoNonterminationAnalysisUNSAT);
		sb.append(": ");
		sb.append(benchmarkData.getValue(s_LassoNonterminationAnalysisUNSAT));
		sb.append("\t");

		sb.append(s_LassoNonterminationAnalysisUNKNOWN);
		sb.append(": ");
		sb.append(benchmarkData.getValue(s_LassoNonterminationAnalysisUNKNOWN));
		sb.append("\t");

		sb.append(s_LassoNonterminationAnalysisTIME);
		sb.append(": ");
		sb.append(prettyprintNanoseconds((Long) benchmarkData.getValue(s_LassoNonterminationAnalysisTIME)));
		sb.append("\t");

		
		return sb.toString();
	}
	
	private String prettyPrintTerminationAnalysisBenchmark(final List<TerminationAnalysisBenchmark> benchmarks) {
		if (benchmarks.isEmpty()) {
			return "not available";
		}
		final StringBuilder sb = new StringBuilder();
		final ICsvProvider<Object> aggr =  aggregateTermBench(benchmarks);
		int offset = 0;
		for (final String title : aggr.getColumnTitles()) {
			sb.append(title);
			sb.append(": ");
			if (title.equals(TerminationAnalysisBenchmark.s_Label_Time)) {
				long value = (long) aggr.getRow(0).get(offset);
				value = value / 1000000;
				sb.append(value);
				sb.append("ms");
			} else if (title.equals(TerminationAnalysisBenchmark.s_Label_ConstraintsSatisfiability)) {
				final LBool value = (LBool) aggr.getRow(0).get(offset);
				sb.append(value);
			} else {
				final int value = (int) aggr.getRow(0).get(offset);
				sb.append(value);
			}
			sb.append(" ");
			offset++;
		}
		return sb.toString();
	}
	
	private ICsvProvider<Object> aggregateTermBench(List<TerminationAnalysisBenchmark> benchmarks) {
		final List<ICsvProvider<Object>> list = new ArrayList<ICsvProvider<Object>>();
		benchmarks = Collections.singletonList(mostMotzkinButUnknownFirst(benchmarks));
		for (final TerminationAnalysisBenchmark benchmark : benchmarks) {
			list.add(benchmark.createCsvProvider());
		}
		final ICsvProvider<Object> allRows = CsvUtils.concatenateRows(list);
		final ICsvProvider<Object> numericColumns = CsvUtils.projectColumn(
				allRows, new String[]{
				TerminationAnalysisBenchmark.s_Label_ConstraintsSatisfiability,
				TerminationAnalysisBenchmark.s_Label_Degree,
				TerminationAnalysisBenchmark.s_Label_Time,
				TerminationAnalysisBenchmark.s_Label_VariablesStem,
				TerminationAnalysisBenchmark.s_Label_VariablesLoop,
				TerminationAnalysisBenchmark.s_Label_DisjunctsStem,
				TerminationAnalysisBenchmark.s_Label_DisjunctsLoop,
				TerminationAnalysisBenchmark.s_Label_SupportingInvariants,
				TerminationAnalysisBenchmark.s_Label_MotzkinApplications });
		return numericColumns;
	}
	
	private TerminationAnalysisBenchmark mostMotzkinButUnknownFirst(final List<TerminationAnalysisBenchmark> benchmarks) {
		boolean foundUnknown = false;
		int mostMotzkin = 0;
		TerminationAnalysisBenchmark mostDifficult = null;
		for (final TerminationAnalysisBenchmark benchmark : benchmarks) {
			if (!foundUnknown) {
				if (benchmark.getConstraintsSatisfiability() == LBool.UNKNOWN) {
					foundUnknown = true;
					mostDifficult = benchmark;
					mostMotzkin = benchmark.getMotzkinApplications();
				} else {
					if (benchmark.getMotzkinApplications() > mostMotzkin) {
						mostDifficult = benchmark;
						mostMotzkin = benchmark.getMotzkinApplications();
					}
				}
			} else {
				if (benchmark.getConstraintsSatisfiability() == LBool.UNKNOWN) {
					if (benchmark.getMotzkinApplications() > mostMotzkin) {
						mostDifficult = benchmark;
						mostMotzkin = benchmark.getMotzkinApplications();
					}
				}
			}
		}
		return mostDifficult;
	}
	
	
	public static class LassoAnalysisResults implements IStatisticsDataProvider, IStatisticsType {
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
		
		public final Map<String, Integer> mMap;
		
		public LassoAnalysisResults() {
			mMap = new LinkedHashMap<String, Integer>();
			mMap.put(s_LassoNonterminating, 0);
			mMap.put(s_TerminationUnknown, 0);
			mMap.put(s_StemFeasibleLoopInfeasible, 0);
			mMap.put(s_StemFeasibleLoopTerminating, 0);
			mMap.put(s_ConcatenationInfeasible, 0);
			mMap.put(s_ConcatInfeasibleLoopTerminating, 0);
			mMap.put(s_StemInfeasibleLoopNonterminating, 0);
			mMap.put(s_StemInfeasibleLoopUnknown, 0);
			mMap.put(s_StemInfeasibleLoopInfeasible, 0);
			mMap.put(s_StemInfeasibleLoopTerminating, 0);
			mMap.put(s_LassoTerminating, 0);
		}
		
		
		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			for (final String key : getKeys()) {
				sb.append(key);
				sb.append(getValue(key));
				sb.append(" ");
			}
			return sb.toString();
		}
		

		public void increment(final String key) {
			final int value = mMap.get(key);
			mMap.put(key, value + 1);
		}
		
//		public void aggregate(LassoAnalysisResults lassoAnalysisResults) {
//			mLassoNonterminating = lassoAnalysisResults.mLassoNonterminating;
//			mTerminationUnknown = lassoAnalysisResults.mTerminationUnknown;
//			mStemFeasibleLoopInfeasible = lassoAnalysisResults.mStemFeasibleLoopInfeasible;
//			mStemFeasibleLoopTerminating = lassoAnalysisResults.mStemFeasibleLoopTerminating;
//			mConcatenationInfeasible = lassoAnalysisResults.mConcatenationInfeasible;
//			mConcatInfeasibleLoopTerminating = lassoAnalysisResults.mConcatInfeasibleLoopTerminating;
//			mStemInfeasibleLoopNonterminating = lassoAnalysisResults.mStemInfeasibleLoopNonterminating;
//			mStemInfeasibleLoopUnknown = lassoAnalysisResults.mStemInfeasibleLoopUnknown;
//			mStemInfeasibleLoopInfeasible = lassoAnalysisResults.mStemInfeasibleLoopInfeasible;
//			mStemInfeasibleLoopTerminating = lassoAnalysisResults.mStemInfeasibleLoopTerminating;
//			mLassoTerminating = lassoAnalysisResults.mLassoTerminating;
//		}

		@Override
		public Collection<String> getKeys() {
			return mMap.keySet();
		}

		@Override
		public Object getValue(final String key) {
			return mMap.get(key);
		}

		@Override
		public IStatisticsType getBenchmarkType() {
			return this;
		}

		@Override
		public Object aggregate(final String key, final Object value1, final Object value2) {
			throw new AssertionError("not yet implemented");
		}

		@Override
		public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
			final LassoAnalysisResults lar = (LassoAnalysisResults) benchmarkData;
			final StringBuilder sb = new StringBuilder();
			for (final String key : lar.getKeys()) {
				sb.append(key);
				sb.append(lar.getValue(key));
				sb.append(" ");
			}
			return sb.toString();
		}


	}

}
