/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.DefaultLassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.AnalysisTechnique;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.DefaultNonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck.HasFixpoint;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.DefaultTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.LexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.NestedTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.PiecewiseTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

public class LassoChecker {

	private final ILogger mLogger;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	enum ContinueDirective {
		REFINE_FINITE, REFINE_BUCHI, REPORT_NONTERMINATION, REPORT_UNKNOWN, REFINE_BOTH
	}

	enum TraceCheckResult {
		FEASIBLE, INFEASIBLE, UNKNOWN, UNCHECKED
	}

	enum SynthesisResult {
		TERMINATING, NONTERMINATING, UNKNOWN, UNCHECKED
	}

	// ////////////////////////////// settings /////////////////////////////////

	private static final boolean mSimplifyStemAndLoop = true;
	/**
	 * If true we check if the loop is terminating even if the stem or the concatenation of stem and loop are already
	 * infeasible. This allows us to use refineFinite and refineBuchi in the same iteration.
	 */
	private final boolean mTryTwofoldRefinement;

	/**
	 * For debugging only. Check for termination arguments even if we found a nontermination argument. This may reveal
	 * unsoundness bugs.
	 */
	private static final boolean s_CheckTerminationEvenIfNonterminating = false;

	private static final boolean s_AvoidNonterminationCheckIfArraysAreContained = true;

	private final InterpolationTechnique mInterpolation;

	private final AnalysisType mRankAnalysisType;
	private final AnalysisType mGntaAnalysisType;
	private final int mGntaDirections;
	private final boolean mTrySimplificationTerminationArgument;

	/**
	 * Try all templates but use the one that was found first. This is only useful to test all templates at once.
	 */
	private final boolean mTemplateBenchmarkMode;

	// ////////////////////////////// input /////////////////////////////////
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final SmtManager mSmtManager;

	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;

	private final BinaryStatePredicateManager mBspm;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	private final NestedLassoRun<CodeBlock, IPredicate> mCounterexample;

	/**
	 * Identifier for this LassoChecker. Can be used to get unique filenames when dumping files.
	 */
	private final String mLassoCheckerIdentifier;

	// ////////////////////////////// auxilliary variables
	// //////////////////////

	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;

	// ////////////////////////////// output /////////////////////////////////

	// private final BuchiModGlobalVarManager mBuchiModGlobalVarManager;

	private final PredicateUnifier mPredicateUnifier;

	private InterpolatingTraceChecker mStemCheck;
	private InterpolatingTraceChecker mLoopCheck;
	private InterpolatingTraceChecker mConcatCheck;

	private NestedRun<CodeBlock, IPredicate> mConcatenatedCounterexample;

	private NonTerminationArgument mNonterminationArgument;

	Collection<Term> mAxioms;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	private final boolean mRemoveSuperfluousSupportingInvariants = true;

	private final LassoCheckResult mLassoCheckResult;

	private final List<PreprocessingBenchmark> mpreprocessingBenchmarks = new ArrayList<>();

	private final List<TerminationAnalysisBenchmark> mTerminationAnalysisBenchmarks = new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> mNonterminationAnalysisBenchmarks = new ArrayList<>();

	public LassoCheckResult getLassoCheckResult() {
		return mLassoCheckResult;
	}

	public InterpolatingTraceChecker getStemCheck() {
		return mStemCheck;
	}

	public InterpolatingTraceChecker getLoopCheck() {
		return mLoopCheck;
	}

	public InterpolatingTraceChecker getConcatCheck() {
		return mConcatCheck;
	}

	public NestedRun<CodeBlock, IPredicate> getConcatenatedCounterexample() {
		assert mConcatenatedCounterexample != null;
		return mConcatenatedCounterexample;
	}

	public BinaryStatePredicateManager getBinaryStatePredicateManager() {
		return mBspm;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		return mNonterminationArgument;
	}

	public List<PreprocessingBenchmark> getPreprocessingBenchmarks() {
		return mpreprocessingBenchmarks;
	}

	public List<TerminationAnalysisBenchmark> getTerminationAnalysisBenchmarks() {
		return mTerminationAnalysisBenchmarks;
	}

	public List<NonterminationAnalysisBenchmark> getNonterminationAnalysisBenchmarks() {
		return mNonterminationAnalysisBenchmarks;
	}

	public LassoChecker(final InterpolationTechnique interpolation, final SmtManager smtManager,
			final ModifiableGlobalVariableManager modifiableGlobalVariableManager, final Collection<Term> axioms,
			final BinaryStatePredicateManager bspm, final NestedLassoRun<CodeBlock, IPredicate> counterexample,
			final String lassoCheckerIdentifier, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final SimplicationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) throws IOException {
		mServices = services;
		mStorage = storage;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mRankAnalysisType = baPref.getEnum(PreferenceInitializer.LABEL_ANALYSIS_TYPE_RANK, AnalysisType.class);
		mGntaAnalysisType = baPref.getEnum(PreferenceInitializer.LABEL_ANALYSIS_TYPE_GNTA, AnalysisType.class);
		mGntaDirections = baPref.getInt(PreferenceInitializer.LABEL_GNTA_DIRECTIONS);

		mTemplateBenchmarkMode = baPref.getBoolean(PreferenceInitializer.LABEL_TEMPLATE_BENCHMARK_MODE);
		mTrySimplificationTerminationArgument = baPref.getBoolean(PreferenceInitializer.LABEL_SIMPLIFY);
		mTryTwofoldRefinement = baPref.getBoolean(PreferenceInitializer.LABEL_TRY_TWOFOLD_REFINEMENT);
		mInterpolation = interpolation;
		mSmtManager = smtManager;
		mModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		mBspm = bspm;
		mCounterexample = counterexample;
		mLassoCheckerIdentifier = lassoCheckerIdentifier;
		mPredicateUnifier = new PredicateUnifier(mServices, mSmtManager.getManagedScript(),
				mSmtManager.getPredicateFactory(), mSmtManager.getBoogie2Smt().getBoogie2SmtSymbolTable(),
				simplificationTechnique, xnfConversionTechnique);
		mTruePredicate = mPredicateUnifier.getTruePredicate();
		mFalsePredicate = mPredicateUnifier.getFalsePredicate();
		mAxioms = axioms;
		mLassoCheckResult = new LassoCheckResult();
		assert mLassoCheckResult.getStemFeasibility() != TraceCheckResult.UNCHECKED;
		assert (mLassoCheckResult.getLoopFeasibility() != TraceCheckResult.UNCHECKED)
				|| (mLassoCheckResult.getLoopFeasibility() != TraceCheckResult.INFEASIBLE && !mTryTwofoldRefinement);
		if (mLassoCheckResult.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			assert mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_FINITE
					|| mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_BOTH;
		} else {
			if (mLassoCheckResult.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
				assert mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_FINITE;
			} else {
				// loop not infeasible
				if (mLassoCheckResult.getLoopTermination() == SynthesisResult.TERMINATING) {
					assert mBspm.providesPredicates();
				} else {
					assert mConcatCheck != null;
					if (mLassoCheckResult.getConcatFeasibility() == TraceCheckResult.INFEASIBLE) {
						assert mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_FINITE
								|| mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_BOTH;
						assert mConcatenatedCounterexample != null;
					} else {
						assert mLassoCheckResult.getContinueDirective() != ContinueDirective.REFINE_FINITE;
					}
				}
			}
		}
	}

	/**
	 * Object for that does computation of lasso check and stores the result. Note that the methods used for the
	 * computation also modify member variables of the superclass.
	 */
	class LassoCheckResult {

		private final TraceCheckResult mStemFeasibility;
		private final TraceCheckResult mLoopFeasibility;
		private final TraceCheckResult mConcatFeasibility;

		private final SynthesisResult mLoopTermination;
		private final SynthesisResult mLassoTermination;

		private final ContinueDirective mContinueDirective;

		public LassoCheckResult() throws IOException {
			final NestedRun<CodeBlock, IPredicate> stem = mCounterexample.getStem();
			mLogger.info("Stem: " + stem);
			final NestedRun<CodeBlock, IPredicate> loop = mCounterexample.getLoop();
			mLogger.info("Loop: " + loop);
			mStemFeasibility = checkStemFeasibility();
			if (mStemFeasibility == TraceCheckResult.INFEASIBLE) {
				mLogger.info("stem already infeasible");
				if (!mTryTwofoldRefinement) {
					mLoopFeasibility = TraceCheckResult.UNCHECKED;
					mConcatFeasibility = TraceCheckResult.UNCHECKED;
					mLoopTermination = SynthesisResult.UNCHECKED;
					mLassoTermination = SynthesisResult.UNCHECKED;
					mContinueDirective = ContinueDirective.REFINE_FINITE;
					return;
				}
			}
			mLoopFeasibility = checkLoopFeasibility();
			if (mLoopFeasibility == TraceCheckResult.INFEASIBLE) {
				mLogger.info("loop already infeasible");
				mConcatFeasibility = TraceCheckResult.UNCHECKED;
				mLoopTermination = SynthesisResult.UNCHECKED;
				mLassoTermination = SynthesisResult.UNCHECKED;
				mContinueDirective = ContinueDirective.REFINE_FINITE;
				return;
			}
			if (mStemFeasibility == TraceCheckResult.INFEASIBLE) {
				assert (mTryTwofoldRefinement);
				final UnmodifiableTransFormula loopTF = computeLoopTF();
				mLoopTermination = checkLoopTermination(loopTF);
				mConcatFeasibility = TraceCheckResult.UNCHECKED;
				mLassoTermination = SynthesisResult.UNCHECKED;
				if (mLoopTermination == SynthesisResult.TERMINATING) {
					mContinueDirective = ContinueDirective.REFINE_BOTH;
					return;
				}
				mContinueDirective = ContinueDirective.REFINE_FINITE;
				return;
			}
			// stem feasible
			mConcatFeasibility = checkConcatFeasibility();
			if (mConcatFeasibility == TraceCheckResult.INFEASIBLE) {
				mLassoTermination = SynthesisResult.UNCHECKED;
				if (mTryTwofoldRefinement) {
					final UnmodifiableTransFormula loopTF = computeLoopTF();
					mLoopTermination = checkLoopTermination(loopTF);
					if (mLoopTermination == SynthesisResult.TERMINATING) {
						mContinueDirective = ContinueDirective.REFINE_BOTH;
						return;
					}
					mContinueDirective = ContinueDirective.REFINE_FINITE;
					return;
				}
				mLoopTermination = SynthesisResult.UNCHECKED;
				mContinueDirective = ContinueDirective.REFINE_FINITE;
				return;
			}
			// concat feasible
			final UnmodifiableTransFormula loopTF = computeLoopTF();
			// checking loop termination before we check lasso
			// termination is a workaround.
			// We want to avoid supporting invariants in possible
			// yet the termination argument simplification of the
			// LassoChecker is not optimal. Hence we first check
			// only the loop, which guarantees that there are no
			// supporting invariants.
			mLoopTermination = checkLoopTermination(loopTF);
			if (mLoopTermination == SynthesisResult.TERMINATING) {
				mLassoTermination = SynthesisResult.UNCHECKED;
				mContinueDirective = ContinueDirective.REFINE_BUCHI;
				return;
			}
			final UnmodifiableTransFormula stemTF = computeStemTF();
			mLassoTermination = checkLassoTermination(stemTF, loopTF);
			if (mLassoTermination == SynthesisResult.TERMINATING) {
				mContinueDirective = ContinueDirective.REFINE_BUCHI;
				return;
			} else if (mLassoTermination == SynthesisResult.NONTERMINATING) {
				mContinueDirective = ContinueDirective.REPORT_NONTERMINATION;
				return;
			} else {
				mContinueDirective = ContinueDirective.REPORT_UNKNOWN;
				return;
			}
		}

		private TraceCheckResult checkStemFeasibility() {
			final NestedRun<CodeBlock, IPredicate> stem = mCounterexample.getStem();
			if (BuchiCegarLoop.emptyStem(mCounterexample)) {
				return TraceCheckResult.FEASIBLE;
			}
			mStemCheck = checkFeasibilityAndComputeInterpolants(stem);
			return translateSatisfiabilityToFeasibility(mStemCheck.isCorrect());
		}

		private TraceCheckResult checkLoopFeasibility() {
			final NestedRun<CodeBlock, IPredicate> loop = mCounterexample.getLoop();
			mLoopCheck = checkFeasibilityAndComputeInterpolants(loop);
			return translateSatisfiabilityToFeasibility(mLoopCheck.isCorrect());
		}

		private TraceCheckResult checkConcatFeasibility() {
			final NestedRun<CodeBlock, IPredicate> stem = mCounterexample.getStem();
			final NestedRun<CodeBlock, IPredicate> loop = mCounterexample.getLoop();
			final NestedRun<CodeBlock, IPredicate> concat = stem.concatenate(loop);
			mConcatCheck = checkFeasibilityAndComputeInterpolants(concat);
			if (mConcatCheck.isCorrect() == LBool.UNSAT) {
				mConcatenatedCounterexample = concat;
			}
			return translateSatisfiabilityToFeasibility(mConcatCheck.isCorrect());
		}

		private TraceCheckResult translateSatisfiabilityToFeasibility(final LBool lBool) {
			switch (lBool) {
			case SAT:
				return TraceCheckResult.FEASIBLE;
			case UNKNOWN:
				return TraceCheckResult.UNKNOWN;
			case UNSAT:
				return TraceCheckResult.INFEASIBLE;
			default:
				throw new AssertionError("unknown case");
			}
		}

		private InterpolatingTraceChecker
				checkFeasibilityAndComputeInterpolants(final NestedRun<CodeBlock, IPredicate> run) {
			InterpolatingTraceChecker result;
			switch (mInterpolation) {
			case Craig_NestedInterpolation:
			case Craig_TreeInterpolation:
				result = new InterpolatingTraceCheckerCraig(mTruePredicate, mFalsePredicate,
						new TreeMap<Integer, IPredicate>(), run.getWord(), mSmtManager,
						mModifiableGlobalVariableManager,
						/*
						 * TODO: When Matthias introduced this parameter he set the argument to
						 * AssertCodeBlockOrder.NOT_INCREMENTALLY. Check if you want to set this to a different value.
						 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices, false, mPredicateUnifier, mInterpolation,
						true, mXnfConversionTechnique, mSimplificationTechnique);
				break;
			case ForwardPredicates:
			case BackwardPredicates:
			case FPandBP:
				result = new TraceCheckerSpWp(mTruePredicate, mFalsePredicate, new TreeMap<Integer, IPredicate>(),
						run.getWord(), mSmtManager, mModifiableGlobalVariableManager,
						/*
						 * TODO: When Matthias introduced this parameter he set the argument to
						 * AssertCodeBlockOrder.NOT_INCREMENTALLY. Check if you want to set this to a different value.
						 */AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, false,
						mPredicateUnifier, mInterpolation, mSmtManager, mXnfConversionTechnique,
						mSimplificationTechnique);
				break;
			default:
				throw new UnsupportedOperationException("unsupported interpolation");
			}
			if (result.getToolchainCancelledExpection() != null) {
				throw result.getToolchainCancelledExpection();
			}
			return result;
		}

		private SynthesisResult checkLoopTermination(final UnmodifiableTransFormula loopTF) throws IOException {
			assert !mBspm.providesPredicates() : "termination already checked";
			final boolean containsArrays = SmtUtils.containsArrayVariables(loopTF.getFormula());
			if (containsArrays) {
				// if there are array variables we will probably run in a huge
				// DNF, so as a precaution we do not check and say unknown
				return SynthesisResult.UNKNOWN;
			}
			return synthesize(false, null, loopTF, containsArrays);
		}

		private SynthesisResult checkLassoTermination(final UnmodifiableTransFormula stemTF,
				final UnmodifiableTransFormula loopTF) throws IOException {
			assert !mBspm.providesPredicates() : "termination already checked";
			assert loopTF != null;
			final boolean containsArrays = SmtUtils.containsArrayVariables(stemTF.getFormula())
					|| SmtUtils.containsArrayVariables(loopTF.getFormula());
			return synthesize(true, stemTF, loopTF, containsArrays);
		}

		public TraceCheckResult getStemFeasibility() {
			return mStemFeasibility;
		}

		public TraceCheckResult getLoopFeasibility() {
			return mLoopFeasibility;
		}

		public TraceCheckResult getConcatFeasibility() {
			return mConcatFeasibility;
		}

		public SynthesisResult getLoopTermination() {
			return mLoopTermination;
		}

		public SynthesisResult getLassoTermination() {
			return mLassoTermination;
		}

		public ContinueDirective getContinueDirective() {
			return mContinueDirective;
		}

	}

	/**
	 * Compute TransFormula that represents the stem.
	 */
	protected UnmodifiableTransFormula computeStemTF() {
		final NestedWord<CodeBlock> stem = mCounterexample.getStem().getWord();
		try {
			final UnmodifiableTransFormula stemTF = computeTF(stem, mSimplifyStemAndLoop, true, false);
			if (SmtUtils.isFalse(stemTF.getFormula())) {
				throw new AssertionError("stemTF is false but stem analysis said: feasible");
			}
			return stemTF;
		} catch (final ToolchainCanceledException tce) {
			throw new ToolchainCanceledException(getClass(),
					tce.getRunningTaskInfo() + " while constructing stem TransFormula");
		}
	}

	/**
	 * Compute TransFormula that represents the loop.
	 */
	protected UnmodifiableTransFormula computeLoopTF() {
		final NestedWord<CodeBlock> loop = mCounterexample.getLoop().getWord();
		try {
			final UnmodifiableTransFormula loopTF = computeTF(loop, mSimplifyStemAndLoop, true, false);
			if (SmtUtils.isFalse(loopTF.getFormula())) {
				throw new AssertionError("loopTF is false but loop analysis said: feasible");
			}
			return loopTF;
		} catch (final ToolchainCanceledException tce) {
			throw new ToolchainCanceledException(getClass(),
					tce.getRunningTaskInfo() + " while constructing loop TransFormula");
		}
	}

	/**
	 * Compute TransFormula that represents the NestedWord word.
	 */
	private UnmodifiableTransFormula computeTF(final NestedWord<CodeBlock> word, final boolean simplify,
			final boolean extendedPartialQuantifierElimination, final boolean withBranchEncoders) {
		final boolean toCNF = false;
		final UnmodifiableTransFormula tf =
				SequentialComposition.getInterproceduralTransFormula(mSmtManager.getBoogie2Smt().getManagedScript(),
						mModifiableGlobalVariableManager, simplify, extendedPartialQuantifierElimination, toCNF,
						withBranchEncoders, mLogger, mServices, word.asList(), mXnfConversionTechnique,
						mSimplificationTechnique, mSmtManager.getBoogie2Smt().getBoogie2SmtSymbolTable());
		return tf;
	}

	private boolean areSupportingInvariantsCorrect() {
		final NestedWord<CodeBlock> stem = mCounterexample.getStem().getWord();
		mLogger.info("Stem: " + stem);
		final NestedWord<CodeBlock> loop = mCounterexample.getLoop().getWord();
		mLogger.info("Loop: " + loop);
		boolean siCorrect = true;
		if (stem.length() == 0) {
			// do nothing
			// TODO: check that si is equivalent to true
		} else {
			for (final SupportingInvariant si : mBspm.getTerminationArgument().getSupportingInvariants()) {
				final IPredicate siPred = mBspm.supportingInvariant2Predicate(si);
				siCorrect &= mBspm.checkSupportingInvariant(siPred, stem, loop, mModifiableGlobalVariableManager);
			}
			// check array index supporting invariants
			for (final Term aisi : mBspm.getTerminationArgument().getArrayIndexSupportingInvariants()) {
				final IPredicate siPred = mBspm.term2Predicate(aisi);
				siCorrect &= mBspm.checkSupportingInvariant(siPred, stem, loop, mModifiableGlobalVariableManager);
			}
		}
		return siCorrect;
	}

	private boolean isRankingFunctionCorrect() {
		final NestedWord<CodeBlock> loop = mCounterexample.getLoop().getWord();
		mLogger.info("Loop: " + loop);
		final boolean rfCorrect = mBspm.checkRankDecrease(loop, mModifiableGlobalVariableManager);
		return rfCorrect;
	}

	private String generateFileBasenamePrefix(final boolean withStem) {
		return mLassoCheckerIdentifier + "_" + (withStem ? "Lasso" : "Loop");
	}

	private ILassoRankerPreferences constructLassoRankerPreferences(final boolean withStem,
			final boolean overapproximateArrayIndexConnection, final NlaHandling nlaHandling,
			final AnalysisTechnique analysis) {
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final ILassoRankerPreferences pref = new DefaultLassoRankerPreferences() {
			@Override
			public boolean isDumpSmtSolverScript() {
				return baPref.getBoolean(PreferenceInitializer.LABEL_DUMP_SCRIPT_TO_FILE);
			}

			@Override
			public String getPathOfDumpedScript() {
				return baPref.getString(PreferenceInitializer.LABEL_DUMP_SCRIPT_PATH);
			}

			@Override
			public String getBaseNameOfDumpedScript() {
				return generateFileBasenamePrefix(withStem);
			}

			@Override
			public boolean isOverapproximateArrayIndexConnection() {
				return overapproximateArrayIndexConnection;
			}

			@Override
			public NlaHandling getNlaHandling() {
				return nlaHandling;
			}

			@Override
			public boolean isUseOldMapElimination() {
				return baPref.getBoolean(PreferenceInitializer.LABEL_USE_OLD_MAP_ELIMINATION);
			}

			@Override
			public boolean isMapElimAddInequalities() {
				return baPref.getBoolean(PreferenceInitializer.LABEL_MAP_ELIMINATION_ADD_INEQUALITIES);
			}

			@Override
			public boolean isMapElimOnlyTrivialImplicationsArrayWrite() {
				return baPref
						.getBoolean(PreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE);
			}

			@Override
			public boolean isMapElimOnlyTrivialImplicationsIndexAssignment() {
				return baPref.getBoolean(
						PreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT);
			}

			@Override
			public boolean isMapElimOnlyIndicesInFormula() {
				return baPref.getBoolean(PreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS);
			}

			@Override
			public boolean isExternalSolver() {
				switch (analysis) {
				case GEOMETRIC_NONTERMINATION_ARGUMENTS: {
					return baPref.getBoolean(PreferenceInitializer.LABEL_USE_EXTERNAL_SOLVER_GNTA);
				}
				case RANKING_FUNCTIONS_SUPPORTING_INVARIANTS: {
					return baPref.getBoolean(PreferenceInitializer.LABEL_USE_EXTERNAL_SOLVER_RANK);
				}
				default:
					throw new UnsupportedOperationException("Analysis type " + analysis + " unknown");
				}
			}

			@Override
			public String getExternalSolverCommand() {
				switch (analysis) {
				case GEOMETRIC_NONTERMINATION_ARGUMENTS: {
					return baPref.getString(PreferenceInitializer.LABEL_EXTERNAL_SOLVER_COMMAND_GNTA);
				}
				case RANKING_FUNCTIONS_SUPPORTING_INVARIANTS: {
					return baPref.getString(PreferenceInitializer.LABEL_EXTERNAL_SOLVER_COMMAND_RANK);
				}
				default:
					throw new UnsupportedOperationException("Analysis type " + analysis + " unknown");
				}
			}
		};
		return pref;
	}

	private TerminationAnalysisSettings constructTASettings() {
		return new TerminationAnalysisSettings(new DefaultTerminationAnalysisSettings() {
			@Override
			public AnalysisType getAnalysis() {
				return mRankAnalysisType;
			}

			@Override
			public int getNumNonStrictInvariants() {
				return 1;
			}

			@Override
			public int getNumStrictInvariants() {
				return 0;
			}

			@Override
			public boolean isNonDecreasingInvariants() {
				return true;
			}

			@Override
			public boolean isSimplifySupportingInvariants() {
				return mTrySimplificationTerminationArgument;
			}

			@Override
			public boolean isSimplifyTerminationArgument() {
				return mTrySimplificationTerminationArgument;
			}
		});
	}

	private NonTerminationAnalysisSettings constructNTASettings() {
		return new NonTerminationAnalysisSettings(new DefaultNonTerminationAnalysisSettings() {
			@Override
			public AnalysisType getAnalysis() {
				return mGntaAnalysisType;
			}

			@Override
			public int getNumberOfGevs() {
				return mGntaDirections;
			}
		});
	}

	private SynthesisResult synthesize(final boolean withStem, UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF, final boolean containsArrays) throws IOException {
		if (mSmtManager.isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of synthesis");
		}

		final Set<IProgramVar> modifiableGlobalsAtHonda = mModifiableGlobalVariableManager.getModifiedBoogieVars(
				((ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0)).getProgramPoint().getProcedure());

		if (!withStem) {
			stemTF = TransFormulaBuilder.getTrivialTransFormula(mSmtManager.getManagedScript());
		}
		// TODO: present this somewhere else
		// int loopVars = loopTF.getFormula().getFreeVars().length;
		// if (stemTF == null) {
		// s_Logger.info("Statistics: no stem, loopVars: " + loopVars);
		// } else {
		// int stemVars = stemTF.getFormula().getFreeVars().length;
		// s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " +
		// loopVars);
		// }

		final FixpointCheck fixpointCheck = new FixpointCheck(mServices, mLogger, mSmtManager.getManagedScript(),
				modifiableGlobalsAtHonda, stemTF, loopTF);
		if (fixpointCheck.getResult() == HasFixpoint.YES) {
			if (withStem) {
				mNonterminationArgument = fixpointCheck.getTerminationArgument();
			}
			return SynthesisResult.NONTERMINATING;
		}

		final boolean doNonterminationAnalysis = !(s_AvoidNonterminationCheckIfArraysAreContained && containsArrays);

		NonTerminationArgument nonTermArgument = null;
		if (doNonterminationAnalysis) {
			LassoAnalysis laNT = null;
			try {
				final boolean overapproximateArrayIndexConnection = false;
				laNT = new LassoAnalysis(mSmtManager.getScript(), mSmtManager.getBoogie2Smt(), stemTF, loopTF,
						modifiableGlobalsAtHonda, mAxioms.toArray(new Term[mAxioms.size()]),
						constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
								NlaHandling.UNDERAPPROXIMATE, AnalysisTechnique.GEOMETRIC_NONTERMINATION_ARGUMENTS),
						mServices, mStorage, mSimplificationTechnique, mXnfConversionTechnique);
				mpreprocessingBenchmarks.add(laNT.getPreprocessingBenchmark());
			} catch (final TermException e) {
				e.printStackTrace();
				throw new AssertionError("TermException " + e);
			}
			try {
				final NonTerminationAnalysisSettings settings = constructNTASettings();
				nonTermArgument = laNT.checkNonTermination(settings);
				final List<NonterminationAnalysisBenchmark> benchs = laNT.getNonterminationAnalysisBenchmarks();
				mNonterminationAnalysisBenchmarks.addAll(benchs);
			} catch (final SMTLIBException e) {
				e.printStackTrace();
				throw new AssertionError("SMTLIBException " + e);
			} catch (final TermException e) {
				e.printStackTrace();
				throw new AssertionError("TermException " + e);
			}
			if (withStem) {
				mNonterminationArgument = nonTermArgument;
			}
			if (!s_CheckTerminationEvenIfNonterminating && nonTermArgument != null) {
				return SynthesisResult.NONTERMINATING;
			}
		}

		LassoAnalysis laT = null;
		try {
			final boolean overapproximateArrayIndexConnection = true;
			laT = new LassoAnalysis(mSmtManager.getScript(), mSmtManager.getBoogie2Smt(), stemTF, loopTF,
					modifiableGlobalsAtHonda, mAxioms.toArray(new Term[mAxioms.size()]),
					constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
							NlaHandling.OVERAPPROXIMATE, AnalysisTechnique.RANKING_FUNCTIONS_SUPPORTING_INVARIANTS),
					mServices, mStorage, mSimplificationTechnique, mXnfConversionTechnique);
			mpreprocessingBenchmarks.add(laT.getPreprocessingBenchmark());
		} catch (final TermException e) {
			e.printStackTrace();
			throw new AssertionError("TermException " + e);
		}

		final List<RankingTemplate> rankingFunctionTemplates = new ArrayList<>();
		rankingFunctionTemplates.add(new AffineTemplate());

		// if (mAllowNonLinearConstraints) {
		// rankingFunctionTemplates.add(new NestedTemplate(1));
		rankingFunctionTemplates.add(new NestedTemplate(2));
		rankingFunctionTemplates.add(new NestedTemplate(3));
		rankingFunctionTemplates.add(new NestedTemplate(4));
		if (mTemplateBenchmarkMode) {
			rankingFunctionTemplates.add(new NestedTemplate(5));
			rankingFunctionTemplates.add(new NestedTemplate(6));
			rankingFunctionTemplates.add(new NestedTemplate(7));
		}

		// rankingFunctionTemplates.add(new MultiphaseTemplate(1));
		rankingFunctionTemplates.add(new MultiphaseTemplate(2));
		rankingFunctionTemplates.add(new MultiphaseTemplate(3));
		rankingFunctionTemplates.add(new MultiphaseTemplate(4));
		if (mTemplateBenchmarkMode) {
			rankingFunctionTemplates.add(new MultiphaseTemplate(5));
			rankingFunctionTemplates.add(new MultiphaseTemplate(6));
			rankingFunctionTemplates.add(new MultiphaseTemplate(7));
		}

		// rankingFunctionTemplates.add(new LexicographicTemplate(1));
		rankingFunctionTemplates.add(new LexicographicTemplate(2));
		rankingFunctionTemplates.add(new LexicographicTemplate(3));
		if (mTemplateBenchmarkMode) {
			rankingFunctionTemplates.add(new LexicographicTemplate(4));
		}

		if (mTemplateBenchmarkMode) {
			rankingFunctionTemplates.add(new PiecewiseTemplate(2));
			rankingFunctionTemplates.add(new PiecewiseTemplate(3));
			rankingFunctionTemplates.add(new PiecewiseTemplate(4));
		}
		// }

		final TerminationArgument termArg =
				tryTemplatesAndComputePredicates(withStem, laT, rankingFunctionTemplates, stemTF, loopTF);
		assert (nonTermArgument == null || termArg == null) : " terminating and nonterminating";
		if (termArg != null) {
			return SynthesisResult.TERMINATING;
		} else if (nonTermArgument != null) {
			return SynthesisResult.NONTERMINATING;
		} else {
			return SynthesisResult.UNKNOWN;
		}
	}

	/**
	 * @param withStem
	 * @param lrta
	 * @param nonTermArgument
	 * @param rankingFunctionTemplates
	 * @param loopTF
	 * @return
	 * @throws AssertionError
	 * @throws IOException
	 */
	private TerminationArgument tryTemplatesAndComputePredicates(final boolean withStem, final LassoAnalysis la,
			final List<RankingTemplate> rankingFunctionTemplates, final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF) throws AssertionError, IOException {
		final String hondaProcedure =
				((ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0)).getProgramPoint().getProcedure();
		final Set<IProgramVar> modifiableGlobals =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(hondaProcedure);

		TerminationArgument firstTerminationArgument = null;
		for (final RankingTemplate rft : rankingFunctionTemplates) {
			TerminationArgument termArg;
			try {
				final TerminationAnalysisSettings settings = constructTASettings();
				termArg = la.tryTemplate(rft, settings);
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							generateRunningTaskInfo(stemTF, loopTF, withStem, rft));
				}
				final List<TerminationAnalysisBenchmark> benchs = la.getTerminationAnalysisBenchmarks();
				mTerminationAnalysisBenchmarks.addAll(benchs);
				if (mTemplateBenchmarkMode) {
					for (final TerminationAnalysisBenchmark bench : benchs) {
						final IResult benchmarkResult =
								new BenchmarkResult<>(Activator.PLUGIN_ID, "LassoTerminationAnalysisBenchmarks", bench);
						mServices.getResultService().reportResult(Activator.PLUGIN_ID, benchmarkResult);
					}
				}
			} catch (final SMTLIBException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("SMTLIBException " + e);
			} catch (final TermException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException " + e);
			}
			if (termArg != null) {
				assert termArg.getRankingFunction() != null;
				assert termArg.getSupportingInvariants() != null;
				mBspm.computePredicates(!withStem, termArg, mRemoveSuperfluousSupportingInvariants, stemTF, loopTF,
						modifiableGlobals);
				assert mBspm.providesPredicates();
				// assert areSupportingInvariantsCorrect() : "incorrect supporting invariant with"
				// + rft.getClass().getSimpleName();
				assert isRankingFunctionCorrect() : "incorrect ranking function with" + rft.getClass().getSimpleName();
				if (!mTemplateBenchmarkMode) {
					return termArg;
				}
				if (firstTerminationArgument == null) {
					firstTerminationArgument = termArg;
				}
				mBspm.clearPredicates();
			}
		}
		if (firstTerminationArgument != null) {
			assert firstTerminationArgument.getRankingFunction() != null;
			assert firstTerminationArgument.getSupportingInvariants() != null;
			mBspm.computePredicates(!withStem, firstTerminationArgument, mRemoveSuperfluousSupportingInvariants, stemTF,
					loopTF, modifiableGlobals);
			assert mBspm.providesPredicates();
			return firstTerminationArgument;
		}
		return null;
	}

	private static String generateRunningTaskInfo(final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF, final boolean withStem, final RankingTemplate rft) {
		return "applying " + rft.getName() + " template (degree " + rft.getDegree() + "), stem dagsize "
				+ new DagSizePrinter(stemTF.getFormula()) + ", loop dagsize " + new DagSizePrinter(loopTF.getFormula());
	}

	// private List<LassoRankerParam> getLassoRankerParameters() {
	// List<LassoRankerParam> lassoRankerParams = new
	// ArrayList<LassoRankerParam>();
	// Preferences pref = new Preferences();
	// pref.numnon_strict_invariants = 2;
	// pref.numstrict_invariants = 0;
	// pref.only_nondecreasing_invariants = false;
	// lassoRankerParams.add(new LassoRankerParam(new AffineTemplate(), pref));
	// return lassoRankerParams;
	// }

	// private class LassoRankerParam {
	// private final RankingFunctionTemplate mRankingFunctionTemplate;
	// private final Preferences mPreferences;
	// public LassoRankerParam(RankingFunctionTemplate rankingFunctionTemplate,
	// Preferences preferences) {
	// super();
	// this.mRankingFunctionTemplate = rankingFunctionTemplate;
	// this.mPreferences = preferences;
	// }
	// public RankingFunctionTemplate getRankingFunctionTemplate() {
	// return mRankingFunctionTemplate;
	// }
	// public Preferences getPreferences() {
	// return mPreferences;
	// }
	// }

}
