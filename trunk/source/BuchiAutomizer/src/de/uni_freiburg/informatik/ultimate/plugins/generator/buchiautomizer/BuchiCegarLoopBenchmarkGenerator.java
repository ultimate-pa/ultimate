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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark.LassoAnalysisResults;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.LassoCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.SynthesisResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

public class BuchiCegarLoopBenchmarkGenerator extends CegarLoopStatisticsGenerator {
	
	int[] mNontrivialModuleStages = new int[5];
	LassoAnalysisResults mLassoAnalysisResults = new LassoAnalysisResults();
	private BackwardCoveringInformation mBciFinite = new BackwardCoveringInformation(0, 0);
	private BackwardCoveringInformation mBciBuchi = new BackwardCoveringInformation(0, 0);
	private int mHighestRank = 0;
	
	private final List<PreprocessingBenchmark> mPreprocessingBenchmarks =
			new ArrayList<PreprocessingBenchmark>();
	private final List<TerminationAnalysisBenchmark> mTerminationAnalysisBenchmarks =
			new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> mNonterminationAnalysisBenchmarks =
			new ArrayList<>();
	private int mLassoNonterminationAnalysisSATFixpoint = 0;
	private int mLassoNonterminationAnalysisSATUnbounded = 0;
	private int mLassoNonterminationAnalysisUNSAT = 0;
	private int mLassoNonterminationAnalysisUNKOWN = 0;
	private long mLassoNonterminationAnalysisTime = 0;
	private int mMinimizationOfDetAutom = 0;
	private int mMinimizationOfNondetAutom = 0;

	
	@Override
	public IStatisticsType getBenchmarkType() {
		return BuchiCegarLoopBenchmark.getInstance();
	}
	
	@Override
	public String[] getStopwatches() {
		final ArrayList<String> al = new ArrayList<String>();
		al.addAll(Arrays.asList(super.getStopwatches()));
		al.add(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
		al.add(BuchiCegarLoopBenchmark.s_BuchiClosure);
		al.add(BuchiCegarLoopBenchmark.s_NontrivialModuleStages);
		al.add(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
		return al.toArray(new String[al.size()]);
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

	@Override
	public Object getValue(final String key) {
		switch (key) {
		case BuchiCegarLoopBenchmark.s_NonLiveStateRemoval:
		case BuchiCegarLoopBenchmark.s_BuchiClosure:
		case BuchiCegarLoopBenchmark.s_LassoAnalysisTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case BuchiCegarLoopBenchmark.s_HighestRank:
			return mHighestRank;
		case BuchiCegarLoopBenchmark.s_NontrivialModuleStages:
			return mNontrivialModuleStages;
		case BuchiCegarLoopBenchmark.s_LassoAnalysisResults:
			return mLassoAnalysisResults;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityFinite:
			return mBciFinite;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityBuchi:
			return mBciBuchi;
		case BuchiCegarLoopBenchmark.s_LassoPreprocessingBenchmarks:
			return mPreprocessingBenchmarks;
		case BuchiCegarLoopBenchmark.s_LassoTerminationAnalysisBenchmarks:
			return mTerminationAnalysisBenchmarks;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisSATFixpoint:
			return mLassoNonterminationAnalysisSATFixpoint;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisSATUnbounded:
			return mLassoNonterminationAnalysisSATUnbounded;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisUNSAT:
			return mLassoNonterminationAnalysisUNSAT;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisUNKNOWN:
			return mLassoNonterminationAnalysisUNKOWN;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisTIME:
			return mLassoNonterminationAnalysisTime;
		case BuchiCegarLoopBenchmark.s_MinimizationsOfDetermnisticAutomatomata:
			return mMinimizationOfDetAutom;
		case BuchiCegarLoopBenchmark.s_MinimizationsOfNondetermnisticAutomatomata:
			return mMinimizationOfNondetAutom;
		default:
			return super.getValue(key);
		}
	}

	public void reportLassoAnalysis(final LassoCheck<? extends IIcfgTransition<?>> lassoCheck) {
		final LassoCheckResult lcr = lassoCheck.getLassoCheckResult();
		mPreprocessingBenchmarks.addAll(lassoCheck.getPreprocessingBenchmarks());
		mTerminationAnalysisBenchmarks.addAll(lassoCheck.getTerminationAnalysisBenchmarks());
		mNonterminationAnalysisBenchmarks.addAll(lassoCheck.getNonterminationAnalysisBenchmarks());
		for (final NonterminationAnalysisBenchmark nab : lassoCheck.getNonterminationAnalysisBenchmarks()) {
			switch (nab.getConstraintsSatisfiability()) {
			case SAT:
				if (nab.isFixpoint()) {
					mLassoNonterminationAnalysisSATFixpoint++;
				} else {
					mLassoNonterminationAnalysisSATUnbounded++;
				}
				break;
			case UNKNOWN:
				mLassoNonterminationAnalysisUNKOWN++;
				break;
			case UNSAT:
				mLassoNonterminationAnalysisUNSAT++;
				break;
			default:
				throw new AssertionError();
			}
			mLassoNonterminationAnalysisTime += nab.getTime();
		}
		final ContinueDirective cd = lcr.getContinueDirective();
		switch (cd) {

		case REFINE_BOTH:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopTerminating);
			} else {
				assert (lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE);
				assert (lcr.getLoopTermination() == SynthesisResult.TERMINATING);
				mLassoAnalysisResults.increment(LassoAnalysisResults.s_ConcatInfeasibleLoopTerminating);
			}
			break;
		case REFINE_BUCHI:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			if (lcr.getLoopTermination() == SynthesisResult.TERMINATING) {
				mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemFeasibleLoopTerminating);
			} else {
				assert lcr.getLassoTermination() == SynthesisResult.TERMINATING;
				mLassoAnalysisResults.increment(LassoAnalysisResults.s_LassoTerminating);
			}
			break;
		case REFINE_FINITE:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
					mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopInfeasible);
				} else {
					if (lcr.getLoopTermination() == SynthesisResult.NONTERMINATING) {
						mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopNonterminating);
					} else {
						assert lcr.getLoopFeasibility() == TraceCheckResult.UNCHECKED
								|| lcr.getLoopFeasibility() == TraceCheckResult.UNKNOWN
								|| lcr.getLoopTermination() == SynthesisResult.UNCHECKED
								|| lcr.getLoopTermination() == SynthesisResult.UNKNOWN
								: "lasso checking: illegal case";
						mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopUnknown);
					}
				}
			} else {
				if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
					mLassoAnalysisResults.increment(LassoAnalysisResults.s_StemFeasibleLoopInfeasible);
				} else {
					assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
					mLassoAnalysisResults.increment(LassoAnalysisResults.s_ConcatenationInfeasible);
				}
			}
			break;
		case REPORT_NONTERMINATION:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoCheck.getNonTerminationArgument() != null;
			assert !lassoCheck.getBinaryStatePredicateManager().providesPredicates();
			mLassoAnalysisResults.increment(LassoAnalysisResults.s_LassoNonterminating);
			break;
		case REPORT_UNKNOWN:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoCheck.getNonTerminationArgument() == null;
			assert !lassoCheck.getBinaryStatePredicateManager().providesPredicates();
			mLassoAnalysisResults.increment(LassoAnalysisResults.s_TerminationUnknown);
			break;
		default:
			throw new AssertionError("unknown case");
		}
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
}
