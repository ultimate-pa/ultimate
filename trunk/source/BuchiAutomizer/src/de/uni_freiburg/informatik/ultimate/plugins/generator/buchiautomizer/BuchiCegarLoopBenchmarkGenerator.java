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
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark.LassoAnalysisResults;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.LassoCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.SynthesisResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class BuchiCegarLoopBenchmarkGenerator extends CegarLoopBenchmarkGenerator {
	
	int[] m_NontrivialModuleStages = new int[5];
	LassoAnalysisResults m_LassoAnalysisResults = new LassoAnalysisResults();
	private BackwardCoveringInformation m_BciFinite = new BackwardCoveringInformation(0, 0);
	private BackwardCoveringInformation m_BciBuchi = new BackwardCoveringInformation(0, 0);
	private int m_HighestRank = 0;
	
	private final List<PreprocessingBenchmark> m_PreprocessingBenchmarks = 
			new ArrayList<PreprocessingBenchmark>();
	private final List<TerminationAnalysisBenchmark> m_TerminationAnalysisBenchmarks =
			new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> m_NonterminationAnalysisBenchmarks =
			new ArrayList<>();
	private int m_LassoNonterminationAnalysisSAT = 0;
	private int m_LassoNonterminationAnalysisUNSAT = 0;
	private int m_LassoNonterminationAnalysisUNKOWN = 0;
	private long m_LassoNonterminationAnalysisTime = 0;

	
	@Override
	public IBenchmarkType getBenchmarkType() {
		return BuchiCegarLoopBenchmark.getInstance();
	}
	
	@Override
	public String[] getStopwatches() {
		ArrayList<String> al = new ArrayList<String>();
		al.addAll(Arrays.asList(super.getStopwatches()));
		al.add(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
		al.add(BuchiCegarLoopBenchmark.s_BuchiClosure);
		al.add(BuchiCegarLoopBenchmark.s_NontrivialModuleStages);
		al.add(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
		return al.toArray(new String[0]);
	}

	public void announceSuccessfullRefinementStage(int stage) {
		m_NontrivialModuleStages[stage]++;
	}
	
	public void addBackwardCoveringInformationFinite(BackwardCoveringInformation bci) {
		m_BciFinite = new BackwardCoveringInformation(m_BciFinite, bci);
	}
	
	public void addBackwardCoveringInformationBuchi(BackwardCoveringInformation bci) {
		m_BciBuchi = new BackwardCoveringInformation(m_BciBuchi, bci);
	}

	@Override
	public Object getValue(String key) {
		switch (key) {
		case BuchiCegarLoopBenchmark.s_NonLiveStateRemoval:
		case BuchiCegarLoopBenchmark.s_BuchiClosure:
		case BuchiCegarLoopBenchmark.s_LassoAnalysisTime:
			try {
				return getElapsedTime(key);
			} catch (StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case BuchiCegarLoopBenchmark.s_HighestRank:
			return m_HighestRank;
		case BuchiCegarLoopBenchmark.s_NontrivialModuleStages:
			return m_NontrivialModuleStages;
		case BuchiCegarLoopBenchmark.s_LassoAnalysisResults:
			return m_LassoAnalysisResults;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityFinite:
			return m_BciFinite;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityBuchi:
			return m_BciBuchi;
		case BuchiCegarLoopBenchmark.s_LassoPreprocessingBenchmarks:
			return m_PreprocessingBenchmarks;
		case BuchiCegarLoopBenchmark.s_LassoTerminationAnalysisBenchmarks:
			return m_TerminationAnalysisBenchmarks;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisSAT:
			return m_LassoNonterminationAnalysisSAT;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisUNSAT:
			return m_LassoNonterminationAnalysisUNSAT;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisUNKNOWN:
			return m_LassoNonterminationAnalysisUNKOWN;
		case BuchiCegarLoopBenchmark.s_LassoNonterminationAnalysisTIME:
			return m_LassoNonterminationAnalysisTime;
		default:
			return super.getValue(key);
		}
	}

	public void reportLassoAnalysis(LassoChecker lassoChecker) {
		LassoCheckResult lcr = lassoChecker.getLassoCheckResult();
		m_PreprocessingBenchmarks.addAll(lassoChecker.getPreprocessingBenchmarks());
		m_TerminationAnalysisBenchmarks.addAll(lassoChecker.getTerminationAnalysisBenchmarks());
		m_NonterminationAnalysisBenchmarks.addAll(lassoChecker.getNonterminationAnalysisBenchmarks());
		for (NonterminationAnalysisBenchmark nab : m_NonterminationAnalysisBenchmarks) {
			switch (nab.getConstraintsSatisfiability()) {
			case SAT:
				m_LassoNonterminationAnalysisSAT++;
				break;
			case UNKNOWN:
				m_LassoNonterminationAnalysisUNKOWN++;
				break;
			case UNSAT:
				m_LassoNonterminationAnalysisUNSAT++;
				break;
			default:
				throw new AssertionError();
			}
			m_LassoNonterminationAnalysisTime += nab.getTime();
		}
		ContinueDirective cd = lcr.getContinueDirective();
		switch (cd) {

		case REFINE_BOTH:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopTerminating);
			} else {
				assert (lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE);
				assert (lcr.getLoopTermination() == SynthesisResult.TERMINATING);
				m_LassoAnalysisResults.increment(LassoAnalysisResults.s_ConcatInfeasibleLoopTerminating);
			}
			break;
		case REFINE_BUCHI:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			if (lcr.getLoopTermination() == SynthesisResult.TERMINATING) {
				m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemFeasibleLoopTerminating);
			} else {
				assert lcr.getLassoTermination() == SynthesisResult.TERMINATING;
				m_LassoAnalysisResults.increment(LassoAnalysisResults.s_LassoTerminating);
			}
			break;
		case REFINE_FINITE:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
					m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopInfeasible);
				} else {
					if (lcr.getLoopTermination() == SynthesisResult.NONTERMINATING) {
						m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopNonterminating);
					} else {
						assert lcr.getLoopFeasibility() == TraceCheckResult.UNCHECKED
								|| lcr.getLoopFeasibility() == TraceCheckResult.UNKNOWN
								|| lcr.getLoopTermination() == SynthesisResult.UNCHECKED
								|| lcr.getLoopTermination() == SynthesisResult.UNKNOWN
								: "lasso checking: illegal case";
						m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemInfeasibleLoopUnknown);
					}
				}
			} else {
				if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
					m_LassoAnalysisResults.increment(LassoAnalysisResults.s_StemFeasibleLoopInfeasible);
				} else {
					assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
					m_LassoAnalysisResults.increment(LassoAnalysisResults.s_ConcatenationInfeasible);
				}
			}
			break;
		case REPORT_NONTERMINATION:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoChecker.getNonTerminationArgument() != null;
			assert !lassoChecker.getBinaryStatePredicateManager().providesPredicates();
			m_LassoAnalysisResults.increment(LassoAnalysisResults.s_LassoNonterminating);
			break;
		case REPORT_UNKNOWN:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoChecker.getNonTerminationArgument() == null;
			assert !lassoChecker.getBinaryStatePredicateManager().providesPredicates();
			m_LassoAnalysisResults.increment(LassoAnalysisResults.s_TerminationUnknown);
			break;
		default:
			throw new AssertionError("unknown case");
		}
	}

	public void reportHighestRank(int highestRank) {
		m_HighestRank = Math.max(m_HighestRank, highestRank);
	}
	
}
