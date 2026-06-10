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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
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
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.DefaultTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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

	// possible outcomes of the fairness trace check
	// TODO: V-Update once I know whats going on with the other enums
	enum FairnessResult {
		FAIR, UNFAIR, UNKNOWN, UNCHECKED
	}

	enum LassoPart {
		STEM, LOOP, CONCAT
	}

	// ////////////////////////////// settings /////////////////////////////////

	private static final boolean SIMPLIFY_STEM_AND_LOOP = true;

	private static final boolean AVOID_NONTERMINATION_CHECK_IF_ARRAYS_ARE_CONTAINED = true;

	private static final boolean TRACE_CHECK_BASED_FIXPOINT_CHECK = true;

	private static final boolean REMOVE_SUPERFLUOUS_SUPPORTING_INVARIANTS = true;

	/**
	 * If true we check if the loop is terminating even if the stem or the concatenation of stem and loop are already
	 * infeasible. This allows us to use refineFinite and refineBuchi in the same iteration.
	 */
	private final boolean mTryTwofoldRefinement;

	private final ILogger mLogger;

	private final SimplificationTechnique mSimplificationTechnique;

	private final AnalysisType mRankAnalysisType;
	private final AnalysisType mGntaAnalysisType;
	private final int mGntaDirections;
	private final boolean mTrySimplificationTerminationArgument;

	/**
	 * Try all templates but use the one that was found first. This is only useful to test all templates at once.
	 */
	private final boolean mTemplateBenchmarkMode;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final CfgSmtToolkit mCsToolkit;

	private final BinaryStatePredicateManager mBspm;

	// TODO V - replace all the mCsToolkit.getManagedScript() s?
	private final ManagedScript mManagedScript;
	private final Function<IPredicate, Object> mGetControlConfiguration;

	/**
	 * Identifier for this LassoCheck. Can be used to get unique filenames when dumping files.
	 */
	private final String mLassoCheckIdentifier;

	private final SmtFunctionsAndAxioms mSmtSymbols;
	private final IUltimateServiceProvider mServices;

	private final ILassoCheckResult<L> mResult;

	private final List<PreprocessingBenchmark> mPreprocessingBenchmarks = new ArrayList<>();

	private final List<TerminationAnalysisBenchmark> mTerminationAnalysisBenchmarks = new ArrayList<>();
	private final List<NonterminationAnalysisBenchmark> mNonterminationAnalysisBenchmarks = new ArrayList<>();

	private final StrategyFactory<L> mRefinementStrategyFactory;

	private final IAutomaton<L, IPredicate> mAbstraction;

	private final TaskIdentifier mTaskIdentifier;

	private final List<RefinementEngineStatisticsGenerator> mRefinementEngineStatistics = new ArrayList<>();
	private final LassoAnalysisResults mLassoAnalysisResults = new LassoAnalysisResults();

	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryForInterpolantAutomaton;

	Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;

	public LassoCheck(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final SmtFunctionsAndAxioms smtSymbols, final BinaryStatePredicateManager bspm,
			final NestedLassoRun<L, IPredicate> counterexample,
			final Function<IPredicate, Object> getControlConfiguration, final String lassoCheckIdentifier,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final StrategyFactory<L> refinementStrategyFactory, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier) throws IOException {
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
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
		// TODO: V - marker added here
		mManagedScript = mCsToolkit.getManagedScript();
		mBspm = bspm;
		mGetControlConfiguration = getControlConfiguration;
		mLassoCheckIdentifier = lassoCheckIdentifier;
		mSmtSymbols = smtSymbols;
		mRefinementStrategyFactory = refinementStrategyFactory;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;

		mPredicateFactory = predicateFactory;
		// TODO: I am unsure about the following flag
		final boolean computeHoareAnnotation = false;
		mStateFactoryForInterpolantAutomaton =
				new PredicateFactoryForInterpolantAutomata(mManagedScript, mPredicateFactory, computeHoareAnnotation);

		mResult = checkTermination(counterexample);
	}

	private ILassoCheckResult<L> checkTermination(final NestedLassoRun<L, IPredicate> counterexample)
			throws IOException {
		final NestedRun<L, IPredicate> stem = counterexample.getStem();
		final NestedRun<L, IPredicate> loop = counterexample.getLoop();
		mLogger.info("Stem: " + stem.getWord());
		mLogger.info("Loop: " + loop.getWord());
		IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> stemCheck;
		final boolean isStemInfeasible;
		if (BuchiAutomizerUtils.isEmptyStem(stem)) {
			stemCheck = null;
			isStemInfeasible = false;
		} else {
			stemCheck = checkStemFeasibility(stem);
			isStemInfeasible = isInfeasible(stemCheck);
		}
		if (isStemInfeasible) {
			mLogger.info("stem already infeasible");
			if (!mTryTwofoldRefinement) {
				mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_INFEASIBLE_LOOP_UNKNOWN);
				return new InfeasibilityResult<>(stemCheck);
			}
		}
		final var loopCheck = checkLoopFeasibility(loop);
		if (isInfeasible(loopCheck)) {
			mLogger.info("loop already infeasible");
			if (isStemInfeasible) {
				mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_INFEASIBLE_LOOP_INFEASIBLE);
				// if both (stem and loop) are infeasible we take the smaller one.
				return loop.getLength() <= stem.getLength() ? new InfeasibilityResult<>(loopCheck)
						: new InfeasibilityResult<>(stemCheck);
			}
			mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_FEASIBLE_LOOP_INFEASIBLE);
			return new InfeasibilityResult<>(loopCheck);
		}
		final IPredicate honda = counterexample.getLoop().getStateAtPosition(0);
		final Set<IProgramNonOldVar> modifiableGlobalsAtHonda = PredicateUtils.streamLocations(honda)
				.flatMap(x -> mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(x.getProcedure()).stream())
				.collect(Collectors.toSet());
		if (isStemInfeasible) {
			assert mTryTwofoldRefinement;
			final UnmodifiableTransFormula loopTF = computeTF(loop.getWord());
			final ILassoCheckResult<L> loopTermination =
					checkLoopTermination(loopTF, counterexample, modifiableGlobalsAtHonda);
			if (loopTermination instanceof final TerminationResult<L> tr) {
				mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_INFEASIBLE_LOOP_TERMINATING);
				return new TerminationAndInfeasibilityResult<>(stemCheck, tr.result());
			}
			mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_INFEASIBLE_LOOP_NONTERMINATING);
			return new InfeasibilityResult<>(stemCheck);
		}
		// stem feasible
		final var concatCheck = checkConcatFeasibility(stem, loop);
		if (isInfeasible(concatCheck)) {
			if (mTryTwofoldRefinement) {
				final UnmodifiableTransFormula loopTF = computeTF(loop.getWord());
				final ILassoCheckResult<L> loopTermination =
						checkLoopTermination(loopTF, counterexample, modifiableGlobalsAtHonda);
				if (loopTermination instanceof final TerminationResult<L> tr) {
					mLassoAnalysisResults.increment(LassoAnalysisResults.CONCATENATION_INFEASIBLE_LOOP_TERMINATING);
					return new TerminationAndInfeasibilityResult<>(concatCheck, tr.result());
				}
			}
			mLassoAnalysisResults.increment(LassoAnalysisResults.CONCATENATION_INFEASIBLE);
			return new InfeasibilityResult<>(concatCheck);
		}
		// concat feasible
		final UnmodifiableTransFormula loopTF = computeTF(loop.getWord());
		final UnmodifiableTransFormula stemTF = computeTF(stem.getWord());
		// ------------------------------------------------------------------------------------------------------------
		// checking loop termination before we check lasso
		// termination is a workaround.
		// We want to avoid supporting invariants in possible
		// yet the termination argument simplification of the
		// LassoChecker is not optimal. Hence we first check
		// only the loop, which guarantees that there are no
		// supporting invariants.

		// TODO: V- Add fairness check for the trace
		// (1) identify loop/nonloop threads
		// (2) Unroll the loop statement by statement, for each honda: - get guards of outgoing non-loop ts - build
		// modified loop, check if it terminates

		// TODO: just add a skip/direct fairness return here--------------------------------------------------------
		assert !mCsToolkit.getConcurrencyInformation().getThreadInstanceMap().isEmpty() : "Concurrent program expected";

		final Set<String> threads = mCsToolkit.getProcedures();

		// identify loop threads = all threads that from which a statement on the loop originates
		final Set<String> loopThreads = new HashSet<>();
		for (final L st : loop.getWord()) {
			loopThreads.add(st.getSource().getProcedure());
		}
		final Set<String> nonLoopThreads = threads;
		nonLoopThreads.removeAll(loopThreads);

		// If there are no non-loop threads, the trace is definitely fair and we can proceed to check termination
		if (!nonLoopThreads.isEmpty()) { // Iterate through the loop states and check for outgoing non-loop edges.
			final NestedRun<L, IPredicate> loopRun = counterexample.getLoop();
			final int loopLen = loopRun.getLength();
			final List<IPredicate> loopStates = loopRun.getStateSequence();

			// get negated disjunction of guards of outgoing non-loop edges. the guard disj. is the same for every
			// state of the loop.
			final Set<IcfgLocation> loopLocs = PredicateUtils.getLocations(loopStates.getFirst());
			final Set<TransFormula> guards = new HashSet<>();
			for (final IcfgLocation threadLoc : loopLocs) {
				if (loopThreads.contains(threadLoc.getProcedure())) {
					continue;
				}
				for (final IcfgEdge edge : threadLoc.getOutgoingEdges()) {
					guards.add(TransFormulaUtils.computeGuard(edge.getTransformula(), mManagedScript, mServices));
				}
			}

			// disjunction of terms should be equivalent to parallel comp of respective TransFormulae
			// TODO: Ask if thats actually true and about branch indicators

			final UnmodifiableTransFormula notGuardDisj = TransFormulaUtils
					.negate(TransFormulaUtils.parallelComposition(mLogger, mServices, mManagedScript, null, false, true,
							guards.toArray(UnmodifiableTransFormula[]::new)), mManagedScript, mServices);
			// TODO: do sth separate if guard disj is true - then we can add whatever loop TS we want to the loop,
			// no?
			// For now, take sup. invariant false and constant ranking function f = 0
			final boolean falseGuard = (SmtUtils.isFalseLiteral(notGuardDisj.getFormula()));
			// TODO: do this properly
			if (mBspm == null) {
				mLogger.warn("Why is bspm null here?");
			}
			if (falseGuard && mBspm.equals(null)) {
				final TerminationArgument constArg = constructTrivialTerminationArgument();
				// TODO: figure out why mBspm is null here
				final UnfairnessResult<L> unf = new UnfairnessResult<>(mBspm.computePredicates(constArg,
						REMOVE_SUPERFLUOUS_SUPPORTING_INVARIANTS, stemTF, loopTF, modifiableGlobalsAtHonda),
						nonLoopThreads, notGuardDisj);
				return unf;

			}
			// we unroll the loop state by state and check if the resulting P(A_fair) terminates
			Set<IProgramNonOldVar> newHondaModGlobals = modifiableGlobalsAtHonda;
			NestedRun<L, IPredicate> newStemRun = counterexample.getStem();
			NestedRun<L, IPredicate> newLoopRun = counterexample.getLoop();
			NestedWord<L> newStem = stem.getWord();
			NestedWord<L> unguardedLoop = loop.getWord();
			// Set<IProgramNonOldVar> modifiableGlobalsAtHonda = mModifiableGlobalsAtHonda;
			for (int i = 0; i < loopLen; i++) {
				// TODO: this is ugly, think of sth better
				// get the transformulae of the current unrolling
				if (i > 0) {
					// TODO: V- add skip if the ts leading to this state doesnt modify guard vars

					// loop transition leading from previous to current honda
					// if this transition does not alter variables from the guard term, we can skip this honda
					final L currentTS = loopRun.getWord().asList().get(i - 1);

					// TODO: �berlegen, was mehr sinn macht
					newStemRun = newStemRun.concatenate(newLoopRun.getSubRun(0, 1));
					newLoopRun = newLoopRun.getSubRun(1, loopLen - 1).concatenate(newLoopRun.getSubRun(0, 1));
					newStem = stem.getWord().concatenate(loop.getWord().getSubWord(0, i));
					unguardedLoop =
							loop.getWord().getSubWord(i, loopLen - 1).concatenate(loop.getWord().getSubWord(0, i));

					final IPredicate newHonda = loopStates.get(i);
					newHondaModGlobals =
							PredicateUtils.streamLocations(newHonda)
									.flatMap(x -> mCsToolkit.getModifiableGlobalsTable()
											.getModifiedBoogieVars(x.getProcedure()).stream())
									.collect(Collectors.toSet());
				}
				final UnmodifiableTransFormula newStemTF = computeTF(newStem);
				final UnmodifiableTransFormula unguardedLoopTF = computeTF(unguardedLoop);
				final UnmodifiableTransFormula guardedLoopTF =
						TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, true, false, false,
								mSimplificationTechnique, List.of(notGuardDisj, unguardedLoopTF));

				// TODO: Was machen wir, wenn das Ding schon ein infeasible prefix (also concat/loop) hat?
				// first check whether the loop part already terminates -- wenn der loop infeasible ist, m�ssen wir
				// den automaten irgendwie anders bauen
				// TODO: das sollte schöner gehen

				final boolean withStem = newStem.length() > 0;
				final boolean contArr = SmtUtils.containsArrayVariables(newStemTF.getFormula())
						|| SmtUtils.containsArrayVariables(loopTF.getFormula());
				final ILassoCheckResult<L> res = synthesize_wo_counterexample(withStem, !withStem, newStem, newStemTF,
						unguardedLoop.length() + 1, guardedLoopTF, contArr, newHondaModGlobals);

				// TODO: V - this could be nicer
				switch (res) {
				case final TerminationResult<L> term:
					// the loop without preconditions is enough to prove unfairness
					return new UnfairnessResult<>(term.result(), nonLoopThreads, notGuardDisj);
				case final InfeasibilityResult<L> inf:
					// TODO: Vfind a sane way to do this
					mLogger.warn("Infeasibility, könnte noch fehlerhaft sein!");
					final TerminationArgument infArg = constructTrivialTerminationArgument();
					final BspmResult infRes = mBspm.computePredicates(infArg, REMOVE_SUPERFLUOUS_SUPPORTING_INVARIANTS,
							newStemTF, unguardedLoopTF, newHondaModGlobals);
					return new UnfairnessResult(infRes, nonLoopThreads, notGuardDisj);
				// TODO: find merge next two cases
				case final NonterminationResult<L> nonterm:
					if (withStem) {
						final ILassoCheckResult<L> progTerm =
								checkFairProgramTermination(nonLoopThreads, newStem, newStemTF, notGuardDisj,
										unguardedLoop, guardedLoopTF, contArr, unguardedLoopTF, newHondaModGlobals, 3);
						if (progTerm instanceof UnfairnessResult<L>) {
							return progTerm;
						}
					}
					break;

				case final UnknownResult<L> uk:
					if (withStem) {
						final ILassoCheckResult<L> progTerm =
								checkFairProgramTermination(nonLoopThreads, newStem, newStemTF, notGuardDisj,
										unguardedLoop, guardedLoopTF, contArr, unguardedLoopTF, newHondaModGlobals, 3);
						if (progTerm instanceof UnfairnessResult<L>) {
							return progTerm;
						}
					}
					break;
				default:
					mLogger.warn("Unexpected type!");
					break;
				}
			}

		}

		// checking loop termination before we check lasso termination is a workaround.
		// We want to avoid supporting invariants in possible yet the termination argument simplification of the
		// LassoChecker is not optimal. Hence we first check only the loop, which guarantees that there are no
		// supporting invariants.
		final ILassoCheckResult<L> loopTermination =
				checkLoopTermination(loopTF, counterexample, modifiableGlobalsAtHonda);
		if (loopTermination instanceof TerminationResult<L>) {
			mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_FEASIBLE_LOOP_TERMINATING);
			return loopTermination;
		}
		final var result = checkLassoTermination(stemTF, loopTF, counterexample, modifiableGlobalsAtHonda);
		switch (result) {
		case final TerminationResult<L> tr ->
				mLassoAnalysisResults.increment(LassoAnalysisResults.STEM_FEASIBLE_LOOP_TERMINATING);
		case final NonterminationResult<L> nr ->
				mLassoAnalysisResults.increment(LassoAnalysisResults.LASSO_NONTERMINATING);
		case final UnknownResult<L> ur -> mLassoAnalysisResults.increment(LassoAnalysisResults.TERMINATION_UNKNOWN);
		default -> throw new AssertionError("Impossible case");
		}
		return result;
	}

	/*
	 * Construct a termination argument with constant ranking function f = 0 and supporting invariant false
	 *
	 */
	private TerminationArgument constructTrivialTerminationArgument() {
		final RankingFunction constRank = new LinearRankingFunction(new AffineFunction());
		final AffineFunction f = new AffineFunction();

		f.setConstant(BigInteger.ONE.negate());
		// it seems that a supporting invariant is an affine ranking function that evaluates to false if it has no
		// coefficients and its constant is <= 0
		final SupportingInvariant falseInv = new SupportingInvariant(f);
		assert falseInv.isFalse() : "Invariant construction failed";
		return new TerminationArgument(constRank, Collections.singletonList(falseInv), null);
	}

	public ILassoCheckResult<L> getLassoCheckResult() {
		return mResult;
	}

	public List<RefinementEngineStatisticsGenerator> getRefinementEngineStatistics() {
		return mRefinementEngineStatistics;
	}

	public LassoAnalysisResults getLassoAnalysisResults() {
		return mLassoAnalysisResults;
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

	private UnmodifiableTransFormula computeTF(final NestedWord<L> word) {
		try {
			final boolean toCNF = false;
			final UnmodifiableTransFormula loopTF =
					SequentialComposition.getInterproceduralTransFormula(mCsToolkit, SIMPLIFY_STEM_AND_LOOP, true,
							toCNF, false, mLogger, mServices, word.asList(), mSimplificationTechnique);
			if (SmtUtils.isFalseLiteral(loopTF.getFormula())) {
				throw new AssertionError("TransFormula is false but analysis said: feasible");
			}
			return loopTF;
		} catch (final ToolchainCanceledException tce) {
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), "constructing TransFormula"));
			throw tce;
		}
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

	private ILassoCheckResult<L> synthesize(final boolean withStem, final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF, final boolean containsArrays,
			final NestedLassoRun<L, IPredicate> counterexample, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda)
			throws IOException {

		final NestedWord<L> stemWord = counterexample.getStem().getWord();
		final int loopLen = counterexample.getLoop().getLength();
		final boolean stemEmpty = BuchiAutomizerUtils.isEmptyStem(counterexample.getStem());
		return synthesize_wo_counterexample(withStem, stemEmpty, stemWord, stemTF, loopLen, loopTF, containsArrays,
				modifiableGlobalsAtHonda);
	}

	// TODO: check if there is an easy way for constructing the A_fair counterexample
	// V - removed the direct use of the counterexample from this method bc it is easier for unfairness
	private ILassoCheckResult<L> synthesize_wo_counterexample(final boolean withStem, final boolean stemEmpty,
			final NestedWord<L> stemWord, UnmodifiableTransFormula stemTF, final int loopLen,
			final UnmodifiableTransFormula loopTF, final boolean containsArrays,
			final Set<IProgramNonOldVar> modifiableGlobalsAtHonda) throws IOException {

		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of synthesis");
		}

		if (!withStem) {
			stemTF = TransFormulaBuilder.getTrivialTransFormula(mManagedScript);
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
				modifiableGlobalsAtHonda, stemTF, loopTF);
		if (fixpointCheck.getResult() == HasFixpoint.YES) {
			if (withStem && TRACE_CHECK_BASED_FIXPOINT_CHECK && !stemEmpty) {
				final FixpointCheck2<L> fixpointCheck2 =
						new FixpointCheck2<>(mServices, mLogger, mCsToolkit, mPredicateFactory, stemWord, loopTF);
				if (fixpointCheck2.getResult() != fixpointCheck.getResult()) {
					throw new AssertionError(String.format(
							"Contradicting results of nontermination analyses: Old %s, New %s, Stem length %s, Loop length %s",
							fixpointCheck.getResult(), fixpointCheck2.getResult(), stemWord.length(), loopLen));
				}
				return new NonterminationResult<>(fixpointCheck2.getTerminationArgument());
			}
			return new NonterminationResult<>(fixpointCheck.getTerminationArgument());
		}

		final boolean doNonterminationAnalysis =
				(!AVOID_NONTERMINATION_CHECK_IF_ARRAYS_ARE_CONTAINED || !containsArrays);

		NonTerminationArgument nonTermArgument = null;
		if (doNonterminationAnalysis) {
			LassoAnalysis laNT = null;
			try {
				final boolean overapproximateArrayIndexConnection = false;
				laNT = new LassoAnalysis(mCsToolkit, stemTF, loopTF, modifiableGlobalsAtHonda, mSmtSymbols,
						constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
								NlaHandling.UNDERAPPROXIMATE, AnalysisTechnique.GEOMETRIC_NONTERMINATION_ARGUMENTS),
						mServices, mSimplificationTechnique);
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
				return new NonterminationResult<>(nonTermArgument);
			}
		}

		LassoAnalysis laT = null;
		try {
			final boolean overapproximateArrayIndexConnection = true;
			laT = new LassoAnalysis(mCsToolkit, stemTF, loopTF, modifiableGlobalsAtHonda, mSmtSymbols,
					constructLassoRankerPreferences(withStem, overapproximateArrayIndexConnection,
							NlaHandling.OVERAPPROXIMATE, AnalysisTechnique.RANKING_FUNCTIONS_SUPPORTING_INVARIANTS),
					mServices, mSimplificationTechnique);
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
			final BspmResult bspmResult = mBspm.computePredicates(termArg, REMOVE_SUPERFLUOUS_SUPPORTING_INVARIANTS,
					stemTF, loopTF, modifiableGlobalsAtHonda);
			return new TerminationResult<>(bspmResult);
		}
		if (nonTermArgument != null) {
			return new NonterminationResult<>(nonTermArgument);

		}
		return new UnknownResult<>();
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

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			checkStemFeasibility(final NestedRun<L, IPredicate> stem) {
		return checkFeasibilityAndComputeInterpolants(stem,
				new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.STEM));
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			checkLoopFeasibility(final NestedRun<L, IPredicate> loop) {
		return checkFeasibilityAndComputeInterpolants(loop,
				new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.LOOP));
	}

	private boolean isInfeasible(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> check) {
		return check.getCounterexampleFeasibility() == LBool.UNSAT;
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			checkConcatFeasibility(final NestedRun<L, IPredicate> stem, final NestedRun<L, IPredicate> loop) {
		return checkFeasibilityAndComputeInterpolants(stem.concatenate(loop),
				new SubtaskLassoCheckIdentifier(mTaskIdentifier, LassoPart.CONCAT));
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> checkFeasibilityAndComputeInterpolants(
			final NestedRun<L, IPredicate> run, final TaskIdentifier taskIdentifier) {
		try {
			final var ctex = mGetControlConfiguration == null ? new Counterexample<>(run.getWord())
					: new Counterexample<>(run.getWord(),
							run.getStateSequence().stream().map(mGetControlConfiguration).collect(Collectors.toList()));
			final ITARefinementStrategy<L> strategy = mRefinementStrategyFactory.constructStrategy(mServices, ctex,
					mAbstraction, taskIdentifier, mStateFactoryForInterpolantAutomaton,
					IPreconditionProvider.constructDefaultPreconditionProvider(),
					IPostconditionProvider.constructDefaultPostconditionProvider());
			final IRefinementEngine<L, NestedWordAutomaton<L, IPredicate>> engine =
					new TraceAbstractionRefinementEngine<>(mServices, mLogger, strategy);
			mRefinementEngineStatistics.add(engine.getRefinementEngineStatistics());
			return engine.getResult();
		} catch (final ToolchainCanceledException tce) {
			final int traceHistogramMax = new HistogramOfIterable<>(run.getWord()).getMax();
			final String taskDescription =
					"analyzing trace of length " + run.getLength() + " with TraceHistMax " + traceHistogramMax;
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;

		}
	}

	private ILassoCheckResult<L> checkLoopTermination(final UnmodifiableTransFormula loopTF,
			final NestedLassoRun<L, IPredicate> counterexample, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda)
			throws IOException {
		final boolean containsArrays = SmtUtils.containsArrayVariables(loopTF.getFormula());
		if (containsArrays) {
			// if there are array variables we will probably run in a huge
			// DNF, so as a precaution we do not check and say unknown
			return new UnknownResult<>();

		}
		return synthesize(false, null, loopTF, containsArrays, counterexample, modifiableGlobalsAtHonda);
	}

	// -------------------- fairness stuff -------------------------------------------------------------------------
	/*
	 * (Approximately) checks whether P(A_fair(trace, guard)) terminates by trying a few 'unrollings' of the program. If
	 * one terminates we check whether its termination argument is sufficient for the whole program.
	 *
	 *
	 *
	 * @param stemTF - transition formula of the stem
	 *
	 * @param loopTF - transition formula for the second loop (the one with negated guard disjunction in front)
	 *
	 * @param unguardedLoopTF - transition formula for the first loop
	 *
	 * @param num_unrollings - how many traces of form [stem (loop)^i (assume not G; loop)^omega] we want to try, should
	 * be greater than 0
	 */
	private ILassoCheckResult<L> checkFairProgramTermination(final Set<String> nonLoopThreads, final NestedWord<L> stem,
			final UnmodifiableTransFormula stemTF, final UnmodifiableTransFormula loopTF, final NestedWord<L> ugLoop,
			final UnmodifiableTransFormula notG, final boolean containsArray,
			final UnmodifiableTransFormula unguardedLoopTF, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda,
			final int num_unrollings) throws IOException {
		UnmodifiableTransFormula urStemTF = stemTF;
		NestedWord<L> urStemWord = stem;
		final NestedWord<L> ugLoopWord = ugLoop;
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> stemCheck;
		// TODO: think about whether we count the stem(loop)^\omega as zeroth or first unrolling
		for (int i = 0; i < num_unrollings; i++) {
			final ILassoCheckResult<L> res = synthesize_wo_counterexample(true, false, urStemWord, urStemTF,
					ugLoop.length() + 1, loopTF, containsArray, modifiableGlobalsAtHonda);
			switch (res) {
			case final UnknownResult<L> uk:
				return new UnknownResult<>();
			// if only this unrolling is infeasible, it doesn't help proving the rest of the program
			case final InfeasibilityResult<L> inf:
				break;
			// One trace of P(A_fair) doesn't terminate --> P doesn't terminate --> G might not hold inf. often
			case final NonterminationResult<L> nonterm:
				// TODO: differentiate between nonterminating and unknown?
				return new UnknownResult<>();
			case final TerminationResult<L> ter:
				// TODO: closed Formula oder Formula?
				final Term supInv = ter.result().getSiConjunction().getFormula();
				// TODO: check whether si is trivial - shouldn't happen, otherwise, why didn't loop only terminate?
				assert !SmtUtils.isTrueLiteral(supInv) : "Nontrivial supporting invariant expected";
				// Note: this only checks whether {si} loop {si} holds - sufficient bc we know that all shorter
				// unrollings terminate

				final boolean sufficient =
						mBspm.isSupportingInvariant(new Term[] { supInv }, unguardedLoopTF, modifiableGlobalsAtHonda);
				if (sufficient) {
					return new UnfairnessResult<>(ter.result(), nonLoopThreads, notG);
				}
			default:
				mLogger.error("wrong type found!");
				break;
			}
			// unroll further
			urStemWord = urStemWord.concatenate(ugLoopWord);
			urStemTF = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, true, false, false,
					mSimplificationTechnique, List.of(urStemTF, unguardedLoopTF));
		}

		return new UnknownResult<>();
	}

	// -------------------------------------------------------------------------------------------------------------

	private ILassoCheckResult<L> checkLassoTermination(final UnmodifiableTransFormula stemTF,
			final UnmodifiableTransFormula loopTF, final NestedLassoRun<L, IPredicate> counterexample,
			final Set<IProgramNonOldVar> modifiableGlobalsAtHonda) throws IOException {
		assert loopTF != null;
		final boolean containsArrays = SmtUtils.containsArrayVariables(stemTF.getFormula())
				|| SmtUtils.containsArrayVariables(loopTF.getFormula());
		return synthesize(true, stemTF, loopTF, containsArrays, counterexample, modifiableGlobalsAtHonda);
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

	public interface ILassoCheckResult<L extends IIcfgTransition<?>> {
		// Just for grouping
	}

	public record InfeasibilityResult<L extends IIcfgTransition<?>>(
			IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementEngineResult)
			implements ILassoCheckResult<L> {
	}

	public record TerminationResult<L extends IIcfgTransition<?>>(BspmResult result) implements ILassoCheckResult<L> {

	}

	public record NonterminationResult<L extends IIcfgTransition<?>>(NonTerminationArgument argument)
			implements ILassoCheckResult<L> {

	}

	public record UnknownResult<L extends IIcfgTransition<?>>() implements ILassoCheckResult<L> {

	}

	// TODO: what form should an Unfairnessresult take?

	/*
	 * @param result bspm result containing the termination argument
	 *
	 * @param nonLoopThreads threads of whom no statement is part of the loop
	 *
	 * @param notG negated disj. of guards of outgoing non-loop statements at the honda
	 */
	public record UnfairnessResult<L extends IIcfgTransition<?>>(BspmResult result, Set<String> nonLoopThreads,
			UnmodifiableTransFormula notG) implements ILassoCheckResult<L> {

	}

	public record TerminationAndInfeasibilityResult<L extends IIcfgTransition<?>>(
			IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementEngineResult, BspmResult result)
			implements ILassoCheckResult<L> {
	}
}
