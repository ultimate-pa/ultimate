package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Arrays;

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
		case BuchiCegarLoopBenchmark.s_NontrivialModuleStages:
			return m_NontrivialModuleStages;
		case BuchiCegarLoopBenchmark.s_LassoAnalysisResults:
			return m_LassoAnalysisResults;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityFinite:
			return m_BciFinite;
		case BuchiCegarLoopBenchmark.s_InterpolantCoveringCapabilityBuchi:
			return m_BciBuchi;
		default:
			return super.getValue(key);
		}
	}

	public void reportLassoAnalysis(LassoChecker lassoChecker) {
		LassoCheckResult lcr = lassoChecker.getLassoCheckResult();
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
					if (lcr.getLoopTermination() == SynthesisResult.NONTERMINATIG) {
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
	
}
