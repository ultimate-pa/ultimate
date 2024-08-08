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
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.DefaultLassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.AnalysisTechnique;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.DefaultNonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck.HasFixpoint;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck2;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.DefaultTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager.BspmResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

public class LassoCheck<L extends IIcfgTransition<?>> {

	public enum ContinueDirective {
		REFINE_FINITE, REFINE_BUCHI, REPORT_NONTERMINATION, REPORT_UNKNOWN, REFINE_BOTH
	}

	public enum TraceCheckResult {
		FEASIBLE, INFEASIBLE, UNKNOWN, UNCHECKED
	}

	enum SynthesisResult {
		TERMINATING, NONTERMINATING, UNKNOWN, UNCHECKED
	}

	enum LassoPart {
		STEM, LOOP, CONCAT
	}

	// ////////////////////////////// settings /////////////////////////////////

	private static final boolean SIMPLIFY_STEM_AND_LOOP = true;

	/**
	 * For debugging only. Check for termination arguments even if we found a nontermination argument. This may reveal
	 * unsoundness bugs.
	 */
	private static final boolean CHECK_TERMINATION_EVEN_IF_NON_TERMINATING = false;

	private static final boolean AVOID_NONTERMINATION_CHECK_IF_ARRAYS_ARE_CONTAINED = true;

	private static final boolean TRACE_CHECK_BASED_FIXPOINT_CHECK = true;

	/**
	 * If true we check if the loop is terminating even if the stem or the concatenation of stem and loop are already
	 * infeasible. This allows us to use refineFinite and refineBuchi in the same iteration.
	 */
	private final boolean mTryTwofoldRefinement;

	private final ILogger mLogger;

	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

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
	private final CfgSmtToolkit mCsToolkit;

	private final BinaryStatePredicateManager mBspm;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	private final NestedLassoRun<L, IPredicate> mCounterexample;

	/**
	 * Identifier for this LassoCheck. Can be used to get unique filenames when dumping files.
	 */
	private final String mLassoCheckIdentifier;

	// ////////////////////////////// auxilliary variables
	// //////////////////////

	// ////////////////////////////// output /////////////////////////////////

	// private final BuchiModGlobalVarManager mBuchiModGlobalVarManager;

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mStemCheck;
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mLoopCheck;
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mConcatCheck;

	private NestedRun<L, IPredicate> mConcatenatedCounterexample;

	private NonTerminationArgument mNonterminationArgument;

	private final SmtFunctionsAndAxioms mSmtSymbols;
	private final IUltimateServiceProvider mServices;
	private final boolean mRemoveSuperfluousSupportingInvariants = true;

	private final LassoCheckResult mLassoCheckResult;

	private final List<PreprocessingBenchmark> mPreprocessingBenchmarks = new ArrayList<>();

	private final List<TerminationAnalysisBenchmark> mTerminationAnalysisBenchmarks = new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> mNonterminationAnalysisBenchmarks = new ArrayList<>();

	private final StrategyFactory<L> mRefinementStrategyFactory;

	private final IAutomaton<L, IPredicate> mAbstraction;

	private final TaskIdentifier mTaskIdentifier;

	// TODO: Do not add statistics but do provide statistics
	private final BuchiCegarLoopBenchmarkGenerator mCegarStatistics;

	private final PredicateFactory mPredicateFactory;

	private final PredicateFactoryForInterpolantAutomata mStateFactoryForInterpolantAutomaton;

	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;

	private BspmResult mBspmResult;

	public LassoCheck(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final SmtFunctionsAndAxioms smtSymbols, final BinaryStatePredicateManager bspm,
			final NestedLassoRun<L, IPredicate> counterexample, final String lassoCheckIdentifier,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final StrategyFactory<L> refinementStrategyFactory,
			final IAutomaton<L, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final BuchiCegarLoopBenchmarkGenerator cegarStatistics) throws IOException {
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mRankAnalysisType =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_ANALYSIS_TYPE_RANK, AnalysisType.class);
		mGntaAnalysisType =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_ANALYSIS_TYPE_GNTA, AnalysisType.class);
		mGntaDirections = baPref.getInt(BuchiAutomizerPreferenceInitializer.LABEL_GNTA_DIRECTIONS);

		mTemplateBenchmarkMode = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_TEMPLATE_BENCHMARK_MODE);
		mTrySimplificationTerminationArgument = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_SIMPLIFY);
		mTryTwofoldRefinement = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_TRY_TWOFOLD_REFINEMENT);
		mCsToolkit = csToolkit;
		mBspm = bspm;
		mCounterexample = counterexample;
		final IPredicate honda = counterexample.getLoop().getStateAtPosition(0);
		mModifiableGlobalsAtHonda = PredicateUtils.streamLocations(honda)
				.flatMap(x -> mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(x.getProcedure()).stream())
				.collect(Collectors.toSet());
		mLassoCheckIdentifier = lassoCheckIdentifier;
		mSmtSymbols = smtSymbols;
		mRefinementStrategyFactory = refinementStrategyFactory;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mCegarStatistics = cegarStatistics;

		mPredicateFactory = predicateFactory;
		// TODO: I am unsure about the following flag
		final boolean computeHoareAnnotation = false;
		mStateFactoryForInterpolantAutomaton = new PredicateFactoryForInterpolantAutomata(mCsToolkit.getManagedScript(),
				mPredicateFactory, computeHoareAnnotation);

		mLassoCheckResult = new LassoCheckResult();
		assert mLassoCheckResult.getStemFeasibility() != TraceCheckResult.UNCHECKED;
		assert mLassoCheckResult.getLoopFeasibility() != TraceCheckResult.UNCHECKED
				|| mLassoCheckResult.getLoopFeasibility() != TraceCheckResult.INFEASIBLE && !mTryTwofoldRefinement;
		if (mLassoCheckResult.getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			assert mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_FINITE
					|| mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_BOTH;
		} else if (mLassoCheckResult.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
			assert mLassoCheckResult.getContinueDirective() == ContinueDirective.REFINE_FINITE;
		} else if (mLassoCheckResult.getLoopTermination() != SynthesisResult.TERMINATING) {
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

	public LassoCheckResult getLassoCheckResult() {
		return mLassoCheckResult;
	}

	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> getStemCheck() {
		return mStemCheck;
	}

	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> getLoopCheck() {
		return mLoopCheck;
	}

	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> getConcatCheck() {
		return mConcatCheck;
	}

	public NestedRun<L, IPredicate> getConcatenatedCounterexample() {
		assert mConcatenatedCounterexample != null;
		return mConcatenatedCounterexample;
	}

	public BspmResult getBspmResult() {
		return mBspmResult;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		return mNonterminationArgument;
	}

	public List<PreprocessingBenchmark> getPreprocessingBenchmarks() {
		return mPreprocessingBenchmarks;
	}

	public List<TerminationAnalysisBenchmark> getTerminationAnalysisBenchmarks() {
		return mTerminationAnalysisBenchmarks;
	}

	public List<NonterminationAnalysisBenchmark> getNonterminationAnalysisBenchmarks() {
		return mNonterminationAnalysisBenchmarks;
	}

	/**
	 * Compute TransFormula that represents the stem.
	 */
	protected UnmodifiableTransFormula computeStemTF() {
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		try {
			final UnmodifiableTransFormula stemTF = computeTF(stem, SIMPLIFY_STEM_AND_LOOP, true, false);
			if (SmtUtils.isFalseLiteral(stemTF.getFormula())) {
				throw new AssertionError("stemTF is false but stem analysis said: feasible");
			}
			return stemTF;
		} catch (final ToolchainCanceledException tce) {
			final String taskDescription = "constructing stem TransFormula";
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}
	}

	/**
	 * Compute TransFormula that represents the loop.
	 */
	protected UnmodifiableTransFormula computeLoopTF() {
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();
		try {
			final UnmodifiableTransFormula loopTF = computeTF(loop, SIMPLIFY_STEM_AND_LOOP, true, false);
			if (SmtUtils.isFalseLiteral(loopTF.getFormula())) {
				throw new AssertionError("loopTF is false but loop analysis said: feasible");
			}
			return loopTF;
		} catch (final ToolchainCanceledException tce) {
			final String taskDescription = "constructing loop TransFormula";
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}
	}

	/**
	 * Compute TransFormula that represents the NestedWord word.
	 */
	private UnmodifiableTransFormula computeTF(final NestedWord<L> word, final boolean simplify,
			final boolean extendedPartialQuantifierElimination, final boolean withBranchEncoders) {
		final boolean toCNF = false;
		return SequentialComposition.getInterproceduralTransFormula(mCsToolkit, simplify,
				extendedPartialQuantifierElimination, toCNF, withBranchEncoders, mLogger, mServices, word.asList(),
				mXnfConversionTechnique, mSimplificationTechnique);
	}

	// private boolean areSupportingInvariantsCorrect() {
	// final NestedWord<L> stem = mCounterexample.getStem().getWord();
	// mLogger.info("Stem: " + stem);
	// final NestedWord<L> loop = mCounterexample.getLoop().getWord();
	// mLogger.info("Loop: " + loop);
	// boolean siCorrect = true;
	// if (stem.length() == 0) {
	// // do nothing
	// // TODO: check that si is equivalent to true
	// } else {
	// for (final SupportingInvariant si : mBspm.getTerminationArgument().getSupportingInvariants()) {
	// final IPredicate siPred = mBspm.supportingInvariant2Predicate(si);
	// siCorrect &= mBspm.checkSupportingInvariant(siPred, stem, loop);
	// }
	// // check array index supporting invariants
	// for (final Term aisi : mBspm.getTerminationArgument().getArrayIndexSupportingInvariants()) {
	// final IPredicate siPred = mBspm.term2Predicate(aisi);
	// siCorrect &= mBspm.checkSupportingInvariant(siPred, stem, loop);
	// }
	// }
	// return siCorrect;
	// }
	//
	// private boolean isRankingFunctionCorrect() {
	// final NestedWord<L> loop = mCounterexample.getLoop().getWord();
	// mLogger.info("Loop: " + loop);
	// return mBspm.checkRankDecrease(loop);
	// }

	private String generateFileBasenamePrefix(final boolean withStem) {
		return mLassoCheckIdentifier + "_" + (withStem ? "Lasso" : "Loop");
	}

	private ILassoRankerPreferences constructLassoRankerPreferences(final boolean withStem,
			final boolean overapproximateArrayIndexConnection, final NlaHandling nlaHandling,
			final AnalysisTechnique analysis) {
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		return new DefaultLassoRankerPreferences() {
			@Override
			public boolean isDumpSmtSolverScript() {
				return baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_DUMP_SCRIPT_TO_FILE);
			}

			@Override
			public String getPathOfDumpedScript() {
				return baPref.getString(BuchiAutomizerPreferenceInitializer.LABEL_DUMP_SCRIPT_PATH);
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
				return baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_USE_OLD_MAP_ELIMINATION);
			}

			@Override
			public boolean isMapElimAddInequalities() {
				return baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_MAP_ELIMINATION_ADD_INEQUALITIES);
			}

			@Override
			public boolean isMapElimOnlyTrivialImplicationsArrayWrite() {
				return baPref.getBoolean(
						BuchiAutomizerPreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE);
			}

			@Override
			public boolean isMapElimOnlyTrivialImplicationsIndexAssignment() {
				return baPref.getBoolean(
						BuchiAutomizerPreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT);
			}

			@Override
			public boolean isMapElimOnlyIndicesInFormula() {
				return baPref
						.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS);
			}

			@Override
			public boolean isExternalSolver() {
				switch (analysis) {
				case GEOMETRIC_NONTERMINATION_ARGUMENTS: {
					return baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_USE_EXTERNAL_SOLVER_GNTA);
				}
				case RANKING_FUNCTIONS_SUPPORTING_INVARIANTS: {
					return baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_USE_EXTERNAL_SOLVER_RANK);
				}
				default:
					throw new UnsupportedOperationException("Analysis type " + analysis + " unknown");
				}
			}

			@Override
			public String getExternalSolverCommand() {
				switch (analysis) {
				case GEOMETRIC_NONTERMINATION_ARGUMENTS: {
					return baPref.getString(BuchiAutomizerPreferenceInitializer.LABEL_EXTERNAL_SOLVER_COMMAND_GNTA);
				}
				case RANKING_FUNCTIONS_SUPPORTING_INVARIANTS: {
					return baPref.getString(BuchiAutomizerPreferenceInitializer.LABEL_EXTERNAL_SOLVER_COMMAND_RANK);
				}
				default:
					throw new UnsupportedOperationException("Analysis type " + analysis + " unknown");
				}
			}
		};
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
		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of synthesis");
		}

		if (!withStem) {
			stemTF = TransFormulaBuilder.getTrivialTransFormula(mCsToolkit.getManagedScript());
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

		final FixpointCheck fixpointCheck = new FixpointCheck(mServices, mLogger, mCsToolkit.getManagedScript(),
				mModifiableGlobalsAtHonda, stemTF, loopTF);
		if (fixpointCheck.getResult() == HasFixpoint.YES) {
			if (withStem) {
				if (TRACE_CHECK_BASED_FIXPOINT_CHECK && mCounterexample.getStem().getWord().length() > 0) {
					final FixpointCheck2<L> fixpointCheck2 = new FixpointCheck2<L>(mServices, mLogger, mCsToolkit,
							mPredicateFactory, mCounterexample.getStem(), loopTF);
					if (fixpointCheck2.getResult() != fixpointCheck.getResult()) {
						throw new AssertionError(String.format(
								"Contradicting results of nontermination analyses: Old %s, New %s, Stem length %s, Loop length %s",
								fixpointCheck.getResult(), fixpointCheck2.getResult(),
								mCounterexample.getStem().getLength(), mCounterexample.getLoop().getLength()));
					}
					mNonterminationArgument = fixpointCheck2.getTerminationArgument();
				} else {
					mNonterminationArgument = fixpointCheck.getTerminationArgument();
				}
			}
			return SynthesisResult.NONTERMINATING;
		}

		final boolean doNonterminationAnalysis =
				(!AVOID_NONTERMINATION_CHECK_IF_ARRAYS_ARE_CONTAINED || !containsArrays);

		NonTerminationArgument nonTermArgument = null;
		if (doNonterminationAnalysis) {
			LassoAnalysis laNT = null;
			try {
				final boolean overapproximateArrayIndexConnection = false;
				laNT = new LassoAnalysis(mCsToolkit, stemTF, loopTF, mModifiableGlobalsAtHonda, mSmtSymbols,
						constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
								NlaHandling.UNDERAPPROXIMATE, AnalysisTechnique.GEOMETRIC_NONTERMINATION_ARGUMENTS),
						mServices, mSimplificationTechnique, mXnfConversionTechnique);
				mPreprocessingBenchmarks.add(laNT.getPreprocessingBenchmark());
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
			if (!CHECK_TERMINATION_EVEN_IF_NON_TERMINATING && nonTermArgument != null) {
				return SynthesisResult.NONTERMINATING;
			}
		}

		LassoAnalysis laT = null;
		try {
			final boolean overapproximateArrayIndexConnection = true;
			laT = new LassoAnalysis(mCsToolkit, stemTF, loopTF, mModifiableGlobalsAtHonda, mSmtSymbols,
					constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
							NlaHandling.OVERAPPROXIMATE, AnalysisTechnique.RANKING_FUNCTIONS_SUPPORTING_INVARIANTS),
					mServices, mSimplificationTechnique, mXnfConversionTechnique);
			mPreprocessingBenchmarks.add(laT.getPreprocessingBenchmark());
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
				tryTemplatesAndComputePredicates(laT, rankingFunctionTemplates, stemTF, loopTF);
		assert nonTermArgument == null || termArg == null : " terminating and nonterminating";
		if (termArg != null) {
			mBspmResult = mBspm.computePredicates(termArg, mRemoveSuperfluousSupportingInvariants, stemTF, loopTF,
					mModifiableGlobalsAtHonda);
			return SynthesisResult.TERMINATING;
		}
		if (nonTermArgument != null) {
			return SynthesisResult.NONTERMINATING;
		}
		return SynthesisResult.UNKNOWN;
	}

	private TerminationArgument tryTemplatesAndComputePredicates(final LassoAnalysis la,
			final List<RankingTemplate> rankingFunctionTemplates, final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF) throws AssertionError, IOException {
		TerminationArgument firstTerminationArgument = null;
		for (final RankingTemplate rft : rankingFunctionTemplates) {
			TerminationArgument termArg;
			try {
				final TerminationAnalysisSettings settings = constructTASettings();
				termArg = la.tryTemplate(rft, settings);
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), generateRunningTaskInfo(stemTF, loopTF, rft));
				}
				final List<TerminationAnalysisBenchmark> benchs = la.getTerminationAnalysisBenchmarks();
				mTerminationAnalysisBenchmarks.addAll(benchs);
				if (mTemplateBenchmarkMode) {
					for (final TerminationAnalysisBenchmark bench : benchs) {
						final IResult benchmarkResult = new StatisticsResult<>(Activator.PLUGIN_ID,
								"LassoTerminationAnalysisBenchmarks", bench);
						mServices.getResultService().reportResult(Activator.PLUGIN_ID, benchmarkResult);
					}
				}
			} catch (final SMTLIBException | TermException e) {
				throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
			}
			if (termArg != null) {
				assert termArg.getRankingFunction() != null;
				assert termArg.getSupportingInvariants() != null;
				// TODO: Check the supporting invariants here. This needs methods from bspm that do not exist anymore.
				// assert areSupportingInvariantsCorrect() : "incorrect supporting invariant with"
				// + rft.getClass().getSimpleName();
				// assert isRankingFunctionCorrect() : "incorrect ranking function with" +
				// rft.getClass().getSimpleName();
				if (!mTemplateBenchmarkMode) {
					return termArg;
				}
				if (firstTerminationArgument == null) {
					firstTerminationArgument = termArg;
				}
			}
		}
		if (firstTerminationArgument != null) {
			assert firstTerminationArgument.getRankingFunction() != null;
			assert firstTerminationArgument.getSupportingInvariants() != null;
			return firstTerminationArgument;
		}
		return null;
	}

	private static String generateRunningTaskInfo(final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF, final RankingTemplate rft) {
		return "applying " + rft.getName() + " template (degree " + rft.getDegree() + "), stem dagsize "
				+ new DagSizePrinter(stemTF.getFormula()) + ", loop dagsize " + new DagSizePrinter(loopTF.getFormula());
	}

	/**
	 * Object for that does computation of lasso check and stores the result. Note that the methods used for the
	 * computation also modify member variables of the superclass.
	 */
	public class LassoCheckResult {

		private final TraceCheckResult mStemFeasibility;
		private final TraceCheckResult mLoopFeasibility;
		private final TraceCheckResult mConcatFeasibility;

		private final SynthesisResult mLoopTermination;
		private final SynthesisResult mLassoTermination;

		private final ContinueDirective mContinueDirective;

		public LassoCheckResult() throws IOException {
			final NestedRun<L, IPredicate> stem = mCounterexample.getStem();
			mLogger.info("Stem: " + stem);
			final NestedRun<L, IPredicate> loop = mCounterexample.getLoop();
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
				assert mTryTwofoldRefinement;
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
			}
			if (mLassoTermination == SynthesisResult.NONTERMINATING) {
				mContinueDirective = ContinueDirective.REPORT_NONTERMINATION;
			} else {
				mContinueDirective = ContinueDirective.REPORT_UNKNOWN;
			}
		}

		private TraceCheckResult checkStemFeasibility() {
			final NestedRun<L, IPredicate> stem = mCounterexample.getStem();
			if (BuchiAutomizerUtils.isEmptyStem(stem)) {
				return TraceCheckResult.FEASIBLE;
			}
			mStemCheck = checkFeasibilityAndComputeInterpolants(stem,
					new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.STEM));
			return translateSatisfiabilityToFeasibility(mStemCheck.getCounterexampleFeasibility());
		}

		private TraceCheckResult checkLoopFeasibility() {
			final NestedRun<L, IPredicate> loop = mCounterexample.getLoop();
			mLoopCheck = checkFeasibilityAndComputeInterpolants(loop,
					new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.LOOP));
			return translateSatisfiabilityToFeasibility(mLoopCheck.getCounterexampleFeasibility());
		}

		private TraceCheckResult checkConcatFeasibility() {
			final NestedRun<L, IPredicate> stem = mCounterexample.getStem();
			final NestedRun<L, IPredicate> loop = mCounterexample.getLoop();
			final NestedRun<L, IPredicate> concat = stem.concatenate(loop);
			mConcatCheck = checkFeasibilityAndComputeInterpolants(concat,
					new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.CONCAT));
			if (mConcatCheck.getCounterexampleFeasibility() == LBool.UNSAT) {
				mConcatenatedCounterexample = concat;
			}
			return translateSatisfiabilityToFeasibility(mConcatCheck.getCounterexampleFeasibility());
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

		private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> checkFeasibilityAndComputeInterpolants(
				final NestedRun<L, IPredicate> run, final TaskIdentifier taskIdentifier) {
			try {
				final ITARefinementStrategy<L> strategy = mRefinementStrategyFactory.constructStrategy(mServices, run,
						mAbstraction, taskIdentifier, mStateFactoryForInterpolantAutomaton,
						IPreconditionProvider.constructDefaultPreconditionProvider(),
						IPostconditionProvider.constructDefaultPostconditionProvider());
				final IRefinementEngine<L, NestedWordAutomaton<L, IPredicate>> engine =
						new TraceAbstractionRefinementEngine<>(mServices, mLogger, strategy);
				mCegarStatistics.addRefinementEngineStatistics(engine.getRefinementEngineStatistics());
				return engine.getResult();
			} catch (final ToolchainCanceledException tce) {
				final int traceHistogramMax = new HistogramOfIterable<>(run.getWord()).getMax();
				final String taskDescription =
						"analyzing trace of length " + run.getLength() + " with TraceHistMax " + traceHistogramMax;
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw tce;
			}
		}

		private SynthesisResult checkLoopTermination(final UnmodifiableTransFormula loopTF) throws IOException {
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

	private static class SubtaskLassoCheckIdentifier extends TaskIdentifier {

		private final LassoPart mLassoPart;

		public SubtaskLassoCheckIdentifier(final TaskIdentifier parentTaskIdentifier, final LassoPart lassoPart) {
			super(parentTaskIdentifier);
			mLassoPart = lassoPart;
		}

		@Override
		protected String getSubtaskIdentifier() {
			return mLassoPart.toString();
		}

	}

}
