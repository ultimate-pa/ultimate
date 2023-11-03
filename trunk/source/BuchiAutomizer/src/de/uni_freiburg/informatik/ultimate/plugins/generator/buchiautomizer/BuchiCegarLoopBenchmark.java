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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar.BuchiCegarLoopResult.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class BuchiCegarLoopBenchmark extends CegarStatisticsType {

	private static final BuchiCegarLoopBenchmark s_Instance = new BuchiCegarLoopBenchmark();

	public static final String RESULT = "Result";
	public static final String HIGHEST_RANK = "HighestRank";
	public static final String NON_LIVE_STATE_REMOVAL = "NonLiveStateRemoval";
	public static final String BUCHI_CLOSURE = "BuchiClosure";
	public static final String NONTRIVIAL_MODUL_STAGES = "NontrivialModuleStages";
	public static final String LASSO_ANALYSIS_TIME = "LassoAnalysisTime";
	public static final String LASSO_ANALYSIS_RESULTS = "LassoAnalysisResults";
	public static final String INTERPOLANT_COVERING_CAPABILITY_FINITE = "InterpolantCoveringCapabilityFinite";
	public static final String INTERPOLANT_COVERING_CAPABILITY_BUCHI = "InterpolantCoveringCapabilityBuchi";
	public static final String LASSO_PREPROCESSING_BENCHMARKS = "LassoPreprocessingBenchmarks";
	public static final String LASSO_TERMINATION_ANALYSIS_BENCHMARKS = "LassoTerminationAnalysisBenchmarks";
	public static final String LASSO_NONTERMINATION_ANALYSIS_BENCHMARKS = "LassoNonterminationAnalysisBenchmarks";
	public static final String LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT = "LassoNonterminationAnalysisSatFixpoint";
	public static final String LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED = "LassoNonterminationAnalysisSatUnbounded";
	public static final String LASSO_NONTERMINATION_ANALYSIS_UNSAT = "LassoNonterminationAnalysisUnsat";
	public static final String LASSO_NONTERMINATION_ANALYSIS_UNKNOWN = "LassoNonterminationAnalysisUnknown";
	public static final String LASSO_NONTERMINATION_ANALYSIS_TIME = "LassoNonterminationAnalysisTime";
	public static final String MINIMIZATION_OF_DETERMINISTIC_AUTOMATA = "MinimizationsOfDetermnisticAutomata";
	public static final String MINIMIZATION_OF_NONDETERMINISTIC_AUTOMATA = "MinimizationsOfNondetermnisticAutomata";

	public static BuchiCegarLoopBenchmark getInstance() {
		return s_Instance;
	}

	@Override
	public Collection<String> getKeys() {
		final ArrayList<String> keyList = new ArrayList<>(super.getKeys());
		keyList.add(HIGHEST_RANK);
		keyList.add(NON_LIVE_STATE_REMOVAL);
		keyList.add(BUCHI_CLOSURE);
		keyList.add(NONTRIVIAL_MODUL_STAGES);
		keyList.add(LASSO_ANALYSIS_TIME);
		keyList.add(LASSO_ANALYSIS_RESULTS);
		keyList.add(INTERPOLANT_COVERING_CAPABILITY_FINITE);
		keyList.add(INTERPOLANT_COVERING_CAPABILITY_BUCHI);
		keyList.add(LASSO_PREPROCESSING_BENCHMARKS);
		keyList.add(LASSO_TERMINATION_ANALYSIS_BENCHMARKS);
		keyList.add(LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT);
		keyList.add(LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED);
		keyList.add(LASSO_NONTERMINATION_ANALYSIS_UNSAT);
		keyList.add(LASSO_NONTERMINATION_ANALYSIS_UNKNOWN);
		keyList.add(LASSO_NONTERMINATION_ANALYSIS_TIME);
		keyList.add(MINIMIZATION_OF_DETERMINISTIC_AUTOMATA);
		keyList.add(MINIMIZATION_OF_NONDETERMINISTIC_AUTOMATA);
		return keyList;
	}

	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		switch (key) {
		case RESULT:
			final Result result1 = (Result) value1;
			final Result result2 = (Result) value2;
			final Set<Result> results = new HashSet<>();
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
		case NONTRIVIAL_MODUL_STAGES: {
			final int[] array1 = (int[]) value1;
			final int[] array2 = (int[]) value2;
			assert array1.length == 4;
			assert array2.length == 4;
			final int[] result = new int[4];
			for (int i = 0; i < 4; i++) {
				result[i] = array1[i] + array1[i];
			}
			return result;
		}
		case INTERPOLANT_COVERING_CAPABILITY_FINITE:
		case INTERPOLANT_COVERING_CAPABILITY_BUCHI:
			final BackwardCoveringInformation bci1 = (BackwardCoveringInformation) value1;
			final BackwardCoveringInformation bci2 = (BackwardCoveringInformation) value2;
			return new BackwardCoveringInformation(bci1, bci2);
		case LASSO_PREPROCESSING_BENCHMARKS:
		case LASSO_TERMINATION_ANALYSIS_BENCHMARKS:
		case HIGHEST_RANK:
		case LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT:
		case LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED:
		case LASSO_NONTERMINATION_ANALYSIS_UNSAT:
		case LASSO_NONTERMINATION_ANALYSIS_UNKNOWN:
		case LASSO_NONTERMINATION_ANALYSIS_TIME:
			throw new AssertionError("not yet implemented");
		default:
			return super.aggregate(key, value1, value2);
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		final StringBuilder sb = new StringBuilder();

		sb.append("BüchiAutomizer plugin needed ");
		final Long overallTime = (Long) benchmarkData.getValue(CegarLoopStatisticsDefinitions.OverallTime.toString());
		sb.append(prettyprintNanoseconds(overallTime));
		sb.append(" and ");
		final Integer overallIterations =
				(Integer) benchmarkData.getValue(CegarLoopStatisticsDefinitions.OverallIterations.toString());
		sb.append(overallIterations);
		sb.append(" iterations. ");

		sb.append(" TraceHistogramMax:");
		final Integer trMax =
				(Integer) benchmarkData.getValue(CegarLoopStatisticsDefinitions.TraceHistogramMax.toString());
		sb.append(trMax);
		sb.append(". ");

		final Long laTime = (Long) benchmarkData.getValue(LASSO_ANALYSIS_TIME);
		sb.append("Analysis of lassos took ");
		sb.append(prettyprintNanoseconds(laTime));
		sb.append(". ");

		final IStatisticsDataProvider ecData = (IStatisticsDataProvider) benchmarkData
				.getValue(CegarLoopStatisticsDefinitions.HoareTripleCheckerStatistics.toString());
		Long ecTime;
		if (ecData.getKeys().isEmpty()) {
			ecTime = 0L;
		} else {
			ecTime = (Long) ecData.getValue(String.valueOf(HoareTripleCheckerStatisticsDefinitions.Time));
		}

		sb.append("Construction of modules took ");
		sb.append(prettyprintNanoseconds(ecTime));
		final Long differenceTime =
				(Long) benchmarkData.getValue(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		sb.append(". ");
		sb.append("Büchi inclusion checks took ");
		sb.append(prettyprintNanoseconds(differenceTime - ecTime));
		sb.append(". ");

		sb.append("Highest rank in rank-based complementation ");
		final Integer highestRank = (Integer) benchmarkData.getValue(HIGHEST_RANK);
		sb.append(highestRank);
		sb.append(". ");

		sb.append("Minimization of det autom ");
		sb.append(benchmarkData.getValue(MINIMIZATION_OF_DETERMINISTIC_AUTOMATA));
		sb.append(". ");

		sb.append("Minimization of nondet autom ");
		sb.append(benchmarkData.getValue(MINIMIZATION_OF_NONDETERMINISTIC_AUTOMATA));
		sb.append(". ");

		sb.append("Automata minimization ");
		sb.append(benchmarkData.getValue(CegarLoopStatisticsDefinitions.AutomataMinimizationStatistics.toString()));
		sb.append(". ");

		sb.append("Non-live state removal took ");
		final Long nonLiveTime = (Long) benchmarkData.getValue(NON_LIVE_STATE_REMOVAL);
		sb.append(prettyprintNanoseconds(nonLiveTime));
		sb.append(" Buchi closure took ");
		final Long buchiClosureTime = (Long) benchmarkData.getValue(BUCHI_CLOSURE);
		sb.append(prettyprintNanoseconds(buchiClosureTime));
		sb.append(". ");

		final SizeIterationPair sip = (SizeIterationPair) benchmarkData
				.getValue(CegarLoopStatisticsDefinitions.BiggestAbstraction.toString());
		sb.append("Biggest automaton had ");
		sb.append(sip.getSize());
		sb.append(" states and ocurred in iteration ");
		sb.append(sip.getIteration());
		sb.append(".\t");

		final int[] stages = (int[]) benchmarkData.getValue(NONTRIVIAL_MODUL_STAGES);
		sb.append("Nontrivial modules had stage ");
		sb.append(Arrays.toString(stages));
		sb.append(".\t");

		final BackwardCoveringInformation bcif =
				(BackwardCoveringInformation) benchmarkData.getValue(INTERPOLANT_COVERING_CAPABILITY_FINITE);
		sb.append(INTERPOLANT_COVERING_CAPABILITY_FINITE);
		sb.append(": ");
		sb.append(bcif.toString());
		sb.append("\t");

		final BackwardCoveringInformation bcib =
				(BackwardCoveringInformation) benchmarkData.getValue(INTERPOLANT_COVERING_CAPABILITY_BUCHI);
		sb.append(INTERPOLANT_COVERING_CAPABILITY_BUCHI);
		sb.append(": ");
		sb.append(bcib.toString());
		sb.append("\t");

		sb.append(CegarLoopStatisticsDefinitions.HoareTripleCheckerStatistics.toString());
		sb.append(": ");
		sb.append(ecData);
		sb.append("\t");

		sb.append(LASSO_ANALYSIS_RESULTS);
		sb.append(": ");
		final LassoAnalysisResults lar = (LassoAnalysisResults) benchmarkData.getValue(LASSO_ANALYSIS_RESULTS);
		sb.append(lar.toString());

		sb.append(LASSO_PREPROCESSING_BENCHMARKS);
		sb.append(": ");
		final List<PreprocessingBenchmark> ppbench =
				(List<PreprocessingBenchmark>) benchmarkData.getValue(LASSO_PREPROCESSING_BENCHMARKS);
		sb.append(PreprocessingBenchmark.prettyprint(ppbench));
		sb.append(LASSO_TERMINATION_ANALYSIS_BENCHMARKS);
		sb.append(": ");
		final List<TerminationAnalysisBenchmark> tabbench =
				(List<TerminationAnalysisBenchmark>) benchmarkData.getValue(LASSO_TERMINATION_ANALYSIS_BENCHMARKS);
		sb.append(prettyPrintTerminationAnalysisBenchmark(tabbench));
		sb.append(LASSO_TERMINATION_ANALYSIS_BENCHMARKS);
		sb.append(": ");

		sb.append(LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT);
		sb.append(": ");
		sb.append(benchmarkData.getValue(LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT));
		sb.append("\t");

		sb.append(LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED);
		sb.append(": ");
		sb.append(benchmarkData.getValue(LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED));
		sb.append("\t");

		sb.append(LASSO_NONTERMINATION_ANALYSIS_UNSAT);
		sb.append(": ");
		sb.append(benchmarkData.getValue(LASSO_NONTERMINATION_ANALYSIS_UNSAT));
		sb.append("\t");

		sb.append(LASSO_NONTERMINATION_ANALYSIS_UNKNOWN);
		sb.append(": ");
		sb.append(benchmarkData.getValue(LASSO_NONTERMINATION_ANALYSIS_UNKNOWN));
		sb.append("\t");

		sb.append(LASSO_NONTERMINATION_ANALYSIS_TIME);
		sb.append(": ");
		sb.append(prettyprintNanoseconds((Long) benchmarkData.getValue(LASSO_NONTERMINATION_ANALYSIS_TIME)));
		sb.append("\t");

		final String initTime = CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime.toString();
		sb.append(initTime);
		sb.append(": ");
		sb.append(prettyprintNanoseconds((Long) benchmarkData.getValue(initTime)));

		return sb.toString();
	}

	private static String prettyPrintTerminationAnalysisBenchmark(final List<TerminationAnalysisBenchmark> benchmarks) {
		if (benchmarks.isEmpty()) {
			return "not available";
		}
		final StringBuilder sb = new StringBuilder();
		final ICsvProvider<Object> aggr = aggregateTermBench(benchmarks);
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

	private static ICsvProvider<Object> aggregateTermBench(List<TerminationAnalysisBenchmark> benchmarks) {
		final List<ICsvProvider<Object>> list = new ArrayList<>();
		benchmarks = Collections.singletonList(mostMotzkinButUnknownFirst(benchmarks));
		for (final TerminationAnalysisBenchmark benchmark : benchmarks) {
			list.add(benchmark.createCsvProvider());
		}
		final ICsvProvider<Object> allRows = CsvUtils.concatenateRows(list);
		final ICsvProvider<Object> numericColumns = CsvUtils.projectColumn(allRows, new String[] {
				TerminationAnalysisBenchmark.s_Label_ConstraintsSatisfiability,
				TerminationAnalysisBenchmark.s_Label_Degree, TerminationAnalysisBenchmark.s_Label_Time,
				TerminationAnalysisBenchmark.s_Label_VariablesStem, TerminationAnalysisBenchmark.s_Label_VariablesLoop,
				TerminationAnalysisBenchmark.s_Label_DisjunctsStem, TerminationAnalysisBenchmark.s_Label_DisjunctsLoop,
				TerminationAnalysisBenchmark.s_Label_SupportingInvariants,
				TerminationAnalysisBenchmark.s_Label_MotzkinApplications });
		return numericColumns;
	}

	private static TerminationAnalysisBenchmark
			mostMotzkinButUnknownFirst(final List<TerminationAnalysisBenchmark> benchmarks) {
		boolean foundUnknown = false;
		int mostMotzkin = 0;
		TerminationAnalysisBenchmark mostDifficult = null;
		for (final TerminationAnalysisBenchmark benchmark : benchmarks) {
			if (!foundUnknown) {
				if (benchmark.getConstraintsSatisfiability() == LBool.UNKNOWN) {
					foundUnknown = true;
					mostDifficult = benchmark;
					mostMotzkin = benchmark.getMotzkinApplications();
				} else if (benchmark.getMotzkinApplications() > mostMotzkin) {
					mostDifficult = benchmark;
					mostMotzkin = benchmark.getMotzkinApplications();
				}
			} else if (benchmark.getConstraintsSatisfiability() == LBool.UNKNOWN) {
				if (benchmark.getMotzkinApplications() > mostMotzkin) {
					mostDifficult = benchmark;
					mostMotzkin = benchmark.getMotzkinApplications();
				}
			}
		}
		return mostDifficult;
	}
}
