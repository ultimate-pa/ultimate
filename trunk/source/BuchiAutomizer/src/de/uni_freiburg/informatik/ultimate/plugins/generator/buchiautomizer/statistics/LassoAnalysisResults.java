package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.statistics;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.SynthesisResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;

public class LassoAnalysisResults extends BaseStatisticsDataProvider {

	@Reflected(prettyName = "nont")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoNonterminating;

	@Reflected(prettyName = "unkn")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTerminationUnknown;

	/**
	 * Cases where (already a single iteration of) the loop is infeasible.
	 */
	@Reflected(prettyName = "SFLI")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemFeasibleLoopInfeasible;

	/**
	 * Cases where the stem is feasible, (a single iteration of) the loop is feasible but the loop is terminating.
	 */
	@Reflected(prettyName = "SFLT")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemFeasibleLoopTerminating;
	/**
	 * Cases where stem and loop are feasible but the concatenation of stem and loop is infeasible.
	 */
	@Reflected(prettyName = "conc")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConcatenationInfeasible;
	/**
	 * Cases where stem and loop are feasible but the concatenation of stem and loop is infeasible and the loop is
	 * terminating.
	 */
	@Reflected(prettyName = "concLT")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConcatInfeasibleLoopTerminating;
	/**
	 * Cases where the stem is infeasible and the loop is nonterminating.
	 */
	@Reflected(prettyName = "SILN")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemInfeasibleLoopNonterminating;
	/**
	 * Cases where the stem is infeasible and the termination/feasibility of the loop is unknown.
	 */
	@Reflected(prettyName = "SILU")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemInfeasibleLoopUnknown;
	/**
	 * Cases where the stem is infeasible and the loop is infeasible.
	 */
	@Reflected(prettyName = "SILI")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemInfeasibleLoopInfeasible;
	/**
	 * Cases where both, stem and loop are infeasible.
	 */
	@Reflected(prettyName = "SILT")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mStemInfeasibleLoopTerminating;
	/**
	 * Cases where the stem and the loop are feasible, the loop itself is nonterminating but the lasso is terminating.
	 */
	@Reflected(prettyName = "lasso")
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mLassoTerminating;

	public LassoAnalysisResults(final IToolchainStorage storage,
			final LassoCheck<? extends IIcfgTransition<?>> lassoCheck) {
		super(storage);
		addLassoCheck(lassoCheck);
	}

	public LassoAnalysisResults(final BaseStatisticsDataProvider sdp,
			final LassoCheck<? extends IIcfgTransition<?>> lassoCheck) {
		super(sdp);
		addLassoCheck(lassoCheck);
	}

	private void addLassoCheck(final LassoCheck<? extends IIcfgTransition<?>> lassoCheck) {
		final LassoCheck<? extends IIcfgTransition<?>>.LassoCheckResult lcr = lassoCheck.getLassoCheckResult();
		final ContinueDirective cd = lcr.getContinueDirective();
		switch (cd) {
		case REFINE_BOTH:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				incrementStemInfeasibleLoopTerminating();
			} else {
				assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
				assert lcr.getLoopTermination() == SynthesisResult.TERMINATING;
				incrementConcatInfeasibleLoopTerminating();
			}
			break;
		case REFINE_BUCHI:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			if (lcr.getLoopTermination() == SynthesisResult.TERMINATING) {
				incrementStemFeasibleLoopTerminating();
			} else {
				assert lcr.getLassoTermination() == SynthesisResult.TERMINATING;
				incrementLassoTerminating();
			}
			break;
		case REFINE_FINITE:
			if (lcr.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
				if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
					incrementStemInfeasibleLoopInfeasible();
				} else if (lcr.getLoopTermination() == SynthesisResult.NONTERMINATING) {
					incrementStemInfeasibleLoopNonterminating();
				} else {
					assert lcr.getLoopFeasibility() == TraceCheckResult.UNCHECKED
							|| lcr.getLoopFeasibility() == TraceCheckResult.UNKNOWN
							|| lcr.getLoopTermination() == SynthesisResult.UNCHECKED
							|| lcr.getLoopTermination() == SynthesisResult.UNKNOWN : "lasso checking: illegal case";
					incrementStemInfeasibleLoopUnknown();
				}
			} else if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
				incrementStemFeasibleLoopInfeasible();
			} else {
				assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
				incrementConcatenationInfeasible();
			}
			break;
		case REPORT_NONTERMINATION:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoCheck.getNonTerminationArgument() != null;
			assert !lassoCheck.getBinaryStatePredicateManager().providesPredicates();
			incrementLassoNonterminating();
			break;
		case REPORT_UNKNOWN:
			assert lcr.getStemFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getLoopFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lcr.getConcatFeasibility() != TraceCheckResult.INFEASIBLE;
			assert lassoCheck.getNonTerminationArgument() == null;
			assert !lassoCheck.getBinaryStatePredicateManager().providesPredicates();
			incrementTerminationUnknown();
			break;
		default:
			throw new AssertionError("unknown case: " + cd);
		}
	}

	public void incrementLassoNonterminating() {
		mLassoNonterminating++;
	}

	public void incrementTerminationUnknown() {
		mTerminationUnknown++;
	}

	public void incrementStemFeasibleLoopInfeasible() {
		mStemFeasibleLoopInfeasible++;
	}

	public void incrementStemFeasibleLoopTerminating() {
		mStemFeasibleLoopTerminating++;
	}

	public void incrementConcatenationInfeasible() {
		mConcatenationInfeasible++;
	}

	public void incrementConcatInfeasibleLoopTerminating() {
		mConcatInfeasibleLoopTerminating++;
	}

	public void incrementStemInfeasibleLoopNonterminating() {
		mStemInfeasibleLoopNonterminating++;
	}

	public void incrementStemInfeasibleLoopUnknown() {
		mStemInfeasibleLoopUnknown++;
	}

	public void incrementStemInfeasibleLoopInfeasible() {
		mStemInfeasibleLoopInfeasible++;
	}

	public void incrementStemInfeasibleLoopTerminating() {
		mStemInfeasibleLoopTerminating++;
	}

	public void incrementLassoTerminating() {
		mLassoTerminating++;
	}

}