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
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.statistics;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class BuchiCegarLoopBenchmarkGenerator extends CegarLoopStatisticsGenerator {

	public static final String s_Result = "Result";
	public static final String HIGHEST_RANK = "HighestRank";
	public static final String TIME_NON_LIVE_STATE_REMOVAL = "NonLiveStateRemoval";
	public static final String TIME_BUCHI_CLOSURE = "BuchiClosure";
	public static final String NONTRIVIAL_MODULE_STAGES = "NontrivialModuleStages";
	public static final String TIME_LASSO_ANALYSIS = "LassoAnalysisTime";
	public static final String LASSO_ANALYSIS_RESULTS = "LassoAnalysisResults";
	public static final String ICC_FINITE = "InterpolantCoveringCapabilityFinite";
	public static final String ICC_BUCHI = "InterpolantCoveringCapabilityBuchi";
	public static final String s_LassoPreprocessingBenchmarks = "LassoPreprocessingBenchmarks";
	public static final String LASSO_TERMINATION_ANALYSIS_BENCHMARKS = "LassoTerminationAnalysisBenchmarks";
	public static final String s_LassoNonterminationAnalysisBenchmarks = "LassoNonterminationAnalysisBenchmarks";
	public static final String LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT = "LassoNonterminationAnalysisSatFixpoint";
	public static final String LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED = "LassoNonterminationAnalysisSatUnbounded";
	public static final String LASSO_NONTERMINATION_ANALYSIS_UNSAT = "LassoNonterminationAnalysisUnsat";
	public static final String LASSO_NONTERMINATION_ANALYSIS_UNKNOWN = "LassoNonterminationAnalysisUnknown";
	public static final String LASSO_NONTERMINATION_ANALYSIS_TIME = "LassoNonterminationAnalysisTime";
	public static final String MINIMIZATION_DET_AUTOMATA = "MinimizationsOfDetermnisticAutomatomata";
	public static final String MINIMIZATION_NONDET_AUTOMATA = "MinimizationsOfNondetermnisticAutomatomata";

	@Reflected(prettyName = ICC_FINITE)
	@Statistics(type = DefaultMeasureDefinitions.BACKWARD_COVERING_INFORMATION)
	private BackwardCoveringInformation mBciFinite = new BackwardCoveringInformation(0, 0);

	@Reflected(prettyName = ICC_BUCHI)
	@Statistics(type = DefaultMeasureDefinitions.BACKWARD_COVERING_INFORMATION)
	private BackwardCoveringInformation mBciBuchi = new BackwardCoveringInformation(0, 0);

	@Reflected(prettyName = HIGHEST_RANK)
	@Statistics(type = DefaultMeasureDefinitions.INT_MAX)
	private int mHighestRank;

	@Reflected(prettyName = TIME_NON_LIVE_STATE_REMOVAL)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mNonLiveStateRemoval = new TimeTracker();

	@Reflected(prettyName = TIME_BUCHI_CLOSURE)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mBuchiClosure = new TimeTracker();

	@Reflected(prettyName = TIME_LASSO_ANALYSIS)
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mLassoAnalysisTime = new TimeTracker();

	@Reflected(prettyName = LASSO_NONTERMINATION_ANALYSIS_TIME)
	@Statistics(type = DefaultMeasureDefinitions.LONG_TIME)
	private long mLassoNonterminationAnalysisTime;

	@Reflected(prettyName = LASSO_NONTERMINATION_ANALYSIS_SAT_FIXPOINT)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoNonterminationAnalysisSatFixpoint;

	@Reflected(prettyName = LASSO_NONTERMINATION_ANALYSIS_SAT_UNBOUNDED)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoNonterminationAnalysisSatUnbounded;

	@Reflected(prettyName = LASSO_NONTERMINATION_ANALYSIS_UNSAT)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoNonterminationAnalysisUnsat;

	@Reflected(prettyName = LASSO_NONTERMINATION_ANALYSIS_UNKNOWN)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoNonterminationAnalysisUnknown;

	@Reflected(prettyName = MINIMIZATION_DET_AUTOMATA)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMinimizationOfDetAutom;

	@Reflected(prettyName = MINIMIZATION_NONDET_AUTOMATA)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMinimizationOfNondetAutom;

	@Reflected(prettyName = NONTRIVIAL_MODULE_STAGES)
	@Statistics(type = DefaultMeasureDefinitions.INT_MULTI_COUNTER)
	private final int[] mNontrivialModuleStages = new int[5];

	@Reflected(prettyName = LASSO_ANALYSIS_RESULTS)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mLassoAnalysisResults;

	@Reflected(prettyName = LASSO_TERMINATION_ANALYSIS_BENCHMARKS)
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mTerminationAnalysisBenchmarks;

	private final List<PreprocessingBenchmark> mPreprocessingBenchmarks = new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> mNonterminationAnalysisBenchmarks = new ArrayList<>();

	public BuchiCegarLoopBenchmarkGenerator(final IToolchainStorage storage) {
		super(storage);
		mLassoAnalysisResults = new StatisticsAggregator(storage);
		mTerminationAnalysisBenchmarks = new StatisticsAggregator(storage);
	}

	public void announceSuccessfullRefinementStage(final int stage) {
		mNontrivialModuleStages[stage]++;
	}

	public void addBackwardCoveringInformationFinite(final BackwardCoveringInformation bci) {
		mBciFinite = new BackwardCoveringInformation(mBciFinite, bci);
	}

	public void addBackwardCoveringInformationBuchi(final BackwardCoveringInformation bci) {
		mBciBuchi = new BackwardCoveringInformation(mBciBuchi, bci);
	}

	public void reportHighestRank(final int highestRank) {
		mHighestRank = Math.max(mHighestRank, highestRank);
	}

	public void reportMinimizationOfDetAutom() {
		mMinimizationOfDetAutom++;
	}

	public void reportMinimizationOfNondetAutom() {
		mMinimizationOfNondetAutom++;
	}

	public void reportLassoAnalysis(final LassoCheck<? extends IIcfgTransition<?>> lassoCheck) {
		mPreprocessingBenchmarks.addAll(lassoCheck.getPreprocessingBenchmarks());
		lassoCheck.getTerminationAnalysisBenchmarks()
				.forEach(a -> mTerminationAnalysisBenchmarks.aggregateStatisticsData(a));
		mNonterminationAnalysisBenchmarks.addAll(lassoCheck.getNonterminationAnalysisBenchmarks());
		for (final NonterminationAnalysisBenchmark nab : lassoCheck.getNonterminationAnalysisBenchmarks()) {
			switch (nab.getConstraintsSatisfiability()) {
			case SAT:
				if (nab.isFixpoint()) {
					mLassoNonterminationAnalysisSatFixpoint++;
				} else {
					mLassoNonterminationAnalysisSatUnbounded++;
				}
				break;
			case UNKNOWN:
				mLassoNonterminationAnalysisUnknown++;
				break;
			case UNSAT:
				mLassoNonterminationAnalysisUnsat++;
				break;
			default:
				throw new AssertionError();
			}
			mLassoNonterminationAnalysisTime += nab.getTime();
		}
		mLassoAnalysisResults.aggregateStatisticsData(new LassoAnalysisResults(this, lassoCheck));
	}

	public void startLassoAnalysisTime() {
		mLassoAnalysisTime.start();
	}

	public void stopLassoAnalysisTime() {
		mLassoAnalysisTime.stop();

	}

	public void startNonLiveStateRemoval() {
		mNonLiveStateRemoval.start();
	}

	public void stopNonLiveStateRemoval() {
		mNonLiveStateRemoval.stop();
	}

	public void startBuchiClosure() {
		mBuchiClosure.start();
	}

	public void stopBuchiClosure() {
		mBuchiClosure.stop();
	}

}
