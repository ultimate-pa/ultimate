/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager.BspmResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBouncer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStyle;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.FairnessWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ILassoCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.InfeasibilityResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.NonterminationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TerminationAndInfeasibilityResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TerminationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.UnfairnessResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.UnknownResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.ReplacingBuchiHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class AbstractBuchiCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected final String mIdentifier;
	protected final boolean mIsConcurrent;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected NestedLassoRun<L, IPredicate> mCounterexample;
	protected final PredicateFactoryForInterpolantAutomata mDefaultStateFactory;
	protected final BuchiCegarLoopBenchmarkGenerator mBenchmarkGenerator;
	protected final PredicateFactory mPredicateFactory;
	protected boolean mIsSemiDeterministic;
	protected boolean mUseDoubleDeckers;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	private final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;

	/**
	 * Construct a termination proof in the form that is required for the Termination Competition.
	 * http://termination-portal.org/wiki/Termination_Competition This proof is finally print in the console output and
	 * can be huge.
	 */
	private final boolean mConstructTermcompProof;
	private final TermcompProofBenchmark mTermcompProofBenchmark;

	private final InterpolationTechnique mInterpolation;

	private BackwardCoveringInformation mBci;

	private final CfgSmtToolkit mCsToolkitWithoutRankVars;
	private final CfgSmtToolkit mCsToolkitWithRankVars;

	private final BinaryStatePredicateManager mBinaryStatePredicateManager;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of of the program.
	 */
	private A mAbstraction;

	private final StrategyFactory<L> mRefinementStrategyFactory;
	private final TaskIdentifier mTaskIdentifier;
	private final BuchiInterpolantAutomatonBuilder<L> mInterpolantAutomatonBuilder;
	private final List<BuchiInterpolantAutomatonConstructionStyle> mBiaConstructionStyleSequence;

	private final Minimization mAutomataMinimizationAfterFeasibilityBasedRefinement;
	private final Minimization mAutomataMinimizationAfterRankBasedRefinement;

	public AbstractBuchiCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz, final A initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		assert services != null;
		mIdentifier = icfg.getIdentifier();
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIdentifier);
		mIsConcurrent = IcfgUtils.isConcurrent(icfg);

		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMDBenchmark = new BuchiAutomizerModuleDecompositionBenchmark(mServices.getBacktranslationService());
		mPredicateFactory = predicateFactory;
		mCsToolkitWithoutRankVars = icfg.getCfgSmtToolkit();
		mCsToolkitWithRankVars = rankVarConstructor.getCsToolkitWithRankVariables();
		mBinaryStatePredicateManager = new BinaryStatePredicateManager(mCsToolkitWithRankVars, predicateFactory,
				rankVarConstructor.getUnseededVariable(), rankVarConstructor.getOldRankVariables(), mServices,
				SIMPLIFICATION_TECHNIQUE);
		mBenchmarkGenerator = benchmarkGenerator;
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		mPref = taPrefs;
		mDefaultStateFactory = new PredicateFactoryForInterpolantAutomata(mCsToolkitWithRankVars.getManagedScript(),
				predicateFactory, mPref.getHoareSettings().computeHoareAnnotation());

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mInterpolation = baPref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);
		mUseDoubleDeckers = !baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_IGNORE_DOWN_STATES);

		InterpolationPreferenceChecker.check(Activator.PLUGIN_NAME, mInterpolation, mServices);
		mConstructTermcompProof = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		mTermcompProofBenchmark = mConstructTermcompProof ? new TermcompProofBenchmark(mServices) : null;

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, SIMPLIFICATION_TECHNIQUE,
						mCsToolkitWithoutRankVars, mPredicateFactory, icfg);
		mRefinementStrategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs, icfg,
				mPredicateFactory, mDefaultStateFactory, transitionClazz);
		mAbstraction = initialAbstraction;
		mInterpolantAutomatonBuilder = new BuchiInterpolantAutomatonBuilder<>(mServices, mCsToolkitWithRankVars,
				SIMPLIFICATION_TECHNIQUE, predicateFactory, mInterpolation);
		mBiaConstructionStyleSequence =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
						BuchiInterpolantAutomatonConstructionStrategy.class).getBiaConstrucionStyleSequence(baPref);
		mAutomataMinimizationAfterFeasibilityBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT,
				Minimization.class);
		mAutomataMinimizationAfterRankBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT,
				Minimization.class);
	}

	/**
	 * Check if {@code abstraction} is empty (i.e. does not accept any word).
	 *
	 * @param abstraction
	 *            The current abstraction
	 * @return true iff {@code abstraction} is empty
	 * @throws AutomataLibraryException
	 */
	protected abstract boolean isAbstractionEmpty(A abstraction) throws AutomataLibraryException;

	/**
	 * Refine the given {@code abstraction} i.e. calculate the difference with the given {@code interpolantAutomaton}
	 * for the case where we detected that a finite prefix of the lasso-shaped counterexample is infeasible. In this
	 * case the module (i.e., the subtrahend {@code interpolantAutomaton} of the difference) will be a weak Büchi
	 * automaton (Büchi automaton where set of final states is a trap). In fact, the module will have only a single
	 * accepting state that is labeled with "false" and that has a self-loop for every letter.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param interpolantAutomaton
	 *            The subtrahend of the difference, a weak Büchi automaton
	 * @return The new refined abstraction
	 * @throws AutomataLibraryException
	 */
	protected abstract A refineFinite(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException;

	/**
	 * Refine the given {@code abstraction} i.e. calculate the difference with the given {@code interpolantAutomaton}
	 * for the case where we detected that the lasso that is represented by the automaton can only be taken finitely
	 * often.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param interpolantAutomaton
	 *            The subtrahend of the difference
	 * @return The new refined abstraction
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A refineBuchi(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException;

	/**
	 * Reduce the size of the given {@code abstraction} w.r.t the given minimization technique
	 * {@code automataMinimization}.
	 *
	 * @param abstraction
	 *            The current abstraction
	 * @param automataMinimization
	 *            The minimization technique
	 * @return A new potentially smaller automaton than {@code abstraction} that still recognizes the same language
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A reduceAbstractionSize(final A abstraction, final Minimization automataMinimization)
			throws AutomataOperationCanceledException;

	public final BuchiCegarLoopResult<L> runCegarLoop() throws IOException {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.getHoareSettings().getHoarePositions());
		mLogger.info("Compute interpolants for " + mInterpolation);
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.getMinimization());

		mIteration = 0;
		final String name = getClass().getSimpleName();
		mLogger.info("======== Iteration %s == of CEGAR loop == %s ========", mIteration, name);

		if (mPref.dumpAutomata()) {
			final String filename = mIdentifier + "_" + name + "Abstraction" + mIteration;
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
					mPref.getAutomataFormat(), "");
		}
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionEmpty(mAbstraction);
		} catch (final AutomataLibraryException e1) {
			mLogger.warn("Verification cancelled");
			mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
			return BuchiCegarLoopResult.constructTimeoutResult(new ToolchainCanceledException(e1.getClassOfThrower()),
					mMDBenchmark, mTermcompProofBenchmark);
		}
		if (initalAbstractionCorrect) {
			mMDBenchmark.reportNoRemainderModule();
			return BuchiCegarLoopResult.constructTerminatingResult(mMDBenchmark, mTermcompProofBenchmark);
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("======== Iteration %s ============", mIteration);
			mBenchmarkGenerator.announceNextIteration();
			boolean abstractionCorrect;
			try {
				abstractionCorrect = isAbstractionEmpty(mAbstraction);
			} catch (final AutomataLibraryException e1) {
				mLogger.warn("Verification cancelled");
				reportRemainderModule(false);
				return BuchiCegarLoopResult.constructTimeoutResult(
						new ToolchainCanceledException(e1.getClassOfThrower()), mMDBenchmark, mTermcompProofBenchmark);
			}
			if (abstractionCorrect) {
				mMDBenchmark.reportNoRemainderModule();
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportNoRemainderModule();
				}
				return BuchiCegarLoopResult.constructTerminatingResult(mMDBenchmark, mTermcompProofBenchmark);
			}

			LassoCheck<L> lassoCheck;
			try {
				final TaskIdentifier taskIdentifier = new SubtaskIterationIdentifier(mTaskIdentifier, mIteration);
				mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
				final String identifier = mIdentifier + "_Iteration" + mIteration;
				lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
						mCsToolkitWithoutRankVars.getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
						mCounterexample, this::getControlConfiguration, identifier, mServices, SIMPLIFICATION_TECHNIQUE,
						mRefinementStrategyFactory, mAbstraction, taskIdentifier);
				if (lassoCheck.getLassoCheckResult() instanceof UnknownResult) {
					// if result was unknown, then try again but this time add one
					// iteration of the loop to the stem.
					// This allows us to verify Vincent's coolant examples
					final TaskIdentifier unwindingTaskIdentifier =
							new SubtaskAdditionalLoopUnwinding(taskIdentifier, 1);
					mLogger.info("Result of lasso check was UNKNOWN. I will concatenate loop to stem and try again.");
					final NestedRun<L, IPredicate> newStem =
							mCounterexample.getStem().concatenate(mCounterexample.getLoop());
					mCounterexample = new NestedLassoRun<>(newStem, mCounterexample.getLoop());
					lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
							mCsToolkitWithoutRankVars.getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
							mCounterexample, this::getControlConfiguration, identifier, mServices,
							SIMPLIFICATION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction,
							unwindingTaskIdentifier);
				}
			} catch (final ToolchainCanceledException e) {
				final int traceHistogramMaxStem =
						new HistogramOfIterable<>(mCounterexample.getStem().getWord()).getMax();
				final int traceHistogramMaxLoop =
						new HistogramOfIterable<>(mCounterexample.getLoop().getWord()).getMax();
				final String taskDescription =
						"analyzing lasso (" + "stem: length " + mCounterexample.getStem().getLength() + " TraceHistMax "
								+ traceHistogramMaxStem + " " + "loop: length " + mCounterexample.getLoop().getLength()
								+ " TraceHistMax " + traceHistogramMaxLoop + ")";
				e.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				return BuchiCegarLoopResult.constructTimeoutResult(e, mMDBenchmark, mTermcompProofBenchmark);
			} finally {
				mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
			}

			final ILassoCheckResult<L> lcr = lassoCheck.getLassoCheckResult();
			mBenchmarkGenerator.reportLassoAnalysis(lassoCheck);
			try {
				switch (lcr) {
				case final TerminationAndInfeasibilityResult<L> tair:
					mAbstraction =
							refineFiniteInternal(refineBuchiInternal(tair.result()), tair.refinementEngineResult());
					break;
				case final InfeasibilityResult<L> ir:
					mAbstraction = refineFiniteInternal(mAbstraction, ir.refinementEngineResult());
					break;
				case final UnfairnessResult<L> unf:
					mAbstraction = refineUnfair(unf);
					break;
				case final TerminationResult<L> tr:
					mAbstraction = refineBuchiInternal(tr.result());
					break;
				case final UnknownResult<L> ur: {
					// Ignore the insufficient thread locations in the counterexample
					final var inUseLocs = new HashSet<>(
							mCsToolkitWithoutRankVars.getConcurrencyInformation().getInUseErrorNodeMap().values());
					final NestedWord<L> stem = getWordWithoutLocs(mCounterexample.getStem(), inUseLocs);
					final NestedWord<L> loop = getWordWithoutLocs(mCounterexample.getLoop(), inUseLocs);
					reportRemainderModule(false);
					return BuchiCegarLoopResult.constructUnknownResult(stem, loop, getOverapproximations(),
							mMDBenchmark, mTermcompProofBenchmark);
				}
				case final NonterminationResult<L> nr: {
					// Ignore the insufficient thread locations in the counterexample
					final var inUseLocs = new HashSet<>(
							mCsToolkitWithoutRankVars.getConcurrencyInformation().getInUseErrorNodeMap().values());
					final NestedWord<L> stem = getWordWithoutLocs(mCounterexample.getStem(), inUseLocs);
					final NestedWord<L> loop = getWordWithoutLocs(mCounterexample.getLoop(), inUseLocs);
					if (getOverapproximations().isEmpty()) {
						reportRemainderModule(true);
						// The loop is empty, i.e. it contains only self-loops in the insufficient thread locations.
						if (loop.length() == 0) {
							return BuchiCegarLoopResult.constructInsufficientThreadsResult();
						}
						return BuchiCegarLoopResult.constructNonTerminatingResult(stem, loop, nr.argument(),
								mMDBenchmark, mTermcompProofBenchmark);
					}
					reportRemainderModule(false);
					return BuchiCegarLoopResult.constructUnknownResult(stem, loop, getOverapproximations(),
							mMDBenchmark, mTermcompProofBenchmark);
				}
				default:
					throw new AssertionError("impossible case");
				}
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());

				if (mPref.dumpAutomata()) {
					final String filename = mIdentifier + "_" + name + "Abstraction" + mIteration;
					BuchiAutomizerUtils.writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
							mPref.getAutomataFormat(), "");
				}

			} catch (final AutomataLibraryException e) {
				return BuchiCegarLoopResult.constructTimeoutResult(
						new ToolchainCanceledException(e.getClassOfThrower()), mMDBenchmark, mTermcompProofBenchmark);
			} catch (final ToolchainCanceledException e) {
				return BuchiCegarLoopResult.constructTimeoutResult(e, mMDBenchmark, mTermcompProofBenchmark);
			}
		}
		return BuchiCegarLoopResult.constructTimeoutResult(
				new ToolchainCanceledException(getClass(), "exceeding the number of iterations"), mMDBenchmark,
				mTermcompProofBenchmark);
	}

	@SuppressWarnings("unchecked")
	private static <L extends IIcfgTransition<?>> NestedWord<L> getWordWithoutLocs(final NestedRun<L, ?> run,
			final Set<IcfgLocation> ignoredLocs) {
		if (ignoredLocs.isEmpty()) {
			return run.getWord();
		}
		final L[] letters = (L[]) run.getWord().asList().stream().filter(x -> !ignoredLocs.contains(x.getTarget()))
				.toArray(IIcfgTransition<?>[]::new);
		return NestedWord.nestedWord(new Word<>(letters));
	}

	private A refineFiniteInternal(final A abstraction,
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> traceCheck)
			throws AutomataLibraryException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final NestedWordAutomaton<L, IPredicate> interpolAutomaton = traceCheck.getInfeasibilityProof();

		final IHoareTripleChecker htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, traceCheck.getPredicateUnifier());

		final DeterministicInterpolantAutomaton<L> determinized = new DeterministicInterpolantAutomaton<>(mServices,
				mCsToolkitWithRankVars, htc, interpolAutomaton, traceCheck.getPredicateUnifier(), false, false);
		final A result;
		try {
			result = reduceAbstractionSize(refineFinite(abstraction, determinized),
					mAutomataMinimizationAfterFeasibilityBasedRefinement);
		} catch (final AutomataOperationCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		} catch (final ToolchainCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		}
		determinized.switchToReadonlyMode();
		if (mPref.dumpAutomata()) {
			final String filename = mIdentifier + "_" + "interpolAutomatonUsedInRefinement" + mIteration + "after";
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, interpolAutomaton, mPref.dumpPath(), filename,
					mPref.getAutomataFormat(), "");
		}
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportFiniteModule(mIteration, interpolAutomaton);
		}
		mMDBenchmark.reportTrivialModule(mIteration, interpolAutomaton.size());
		assert NwaFloydHoareValidityCheck.forInterpolantAutomaton(mServices, mCsToolkitWithRankVars.getManagedScript(),
				new IncrementalHoareTripleChecker(mCsToolkitWithRankVars, false), traceCheck.getPredicateUnifier(),
				interpolAutomaton, true).getResult();
		mBenchmarkGenerator.addEdgeCheckerData(htc.getStatistics());
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		return result;
	}

	/**
	 * Essentially a simplified version of refineBuchiInternal for Unfairness
	 *
	 * @param unfairRes
	 *            the result of an unfairness analysis
	 *
	 * @return the difference between the previous abstraction and the generalized unfair trace module
	 */
	private A refineUnfair(final UnfairnessResult<L> unfairRes) throws AutomataLibraryException {
		final A newAbstr;
		final IPredicate hondaPredicate = unfairRes.result().getHondaPredicate();
		final IPredicate rankEqAndSi = unfairRes.result().getRankEqAndSi();

		assert !SmtUtils.isFalseLiteral(unfairRes.result().getStemPrecondition().getFormula());
		// assert !SmtUtils.isFalseLiteral(hondaPredicate.getFormula()); -- we allow that for now
		// assert !SmtUtils.isFalseLiteral(rankEqAndSi.getFormula());
		// TODO: was sind die dump automata einstellungen?

		// hondaPredicate already contains the supporting invariants
		final RankingFunction rank = unfairRes.result().getTerminationArgument().getRankingFunction();
		final Script script = mCsToolkitWithRankVars.getManagedScript().getScript();

		mMDBenchmark.reportRankingFunction(mIteration, rank, script);
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		// for now we ignore the constructions styles

		// TODO: find out whether messing with the initial predicates causes any damage and code this nicer
		// -->it does, when computing the difference we get complaints that the predicates are unknown...
		// the predicate unifier can't take different predicates with the same formula as input
		final List<IPredicate> initialPredicates = new ArrayList<>();
		initialPredicates.add(unfairRes.result().getStemPrecondition());
		// initialPredicates.add(unfairRes.result().getStemPostcondition());
		initialPredicates.add(unfairRes.result().getRankDecreaseAndBound());
		initialPredicates.add(hondaPredicate);

		/*
		 * if (!SmtUtils.isFalseLiteral(hondaPredicate.getFormula())) { initialPredicates.add(hondaPredicate); }
		 */
		if (!SmtUtils.isFalseLiteral(unfairRes.result().getSiConjunction().getFormula())) {
			initialPredicates.add(rankEqAndSi);
			initialPredicates.add(unfairRes.result().getSiConjunction());
		}
		final IPredicate[] predArr = initialPredicates.stream().toArray(IPredicate[]::new);
		final PredicateUnifier pu = new PredicateUnifier(mLogger, mServices, mCsToolkitWithRankVars.getManagedScript(),
				mPredicateFactory, mCsToolkitWithRankVars.getSymbolTable(), SIMPLIFICATION_TECHNIQUE, predArr);
		final IPredicate[] unifiedStemInterpolants = getStemInterpolants(mCounterexample.getStem(),
				unfairRes.result().getStemPrecondition(), unfairRes.result().getStemPostcondition(), pu);

		final IPredicate[] unifiedLoopInterpolants =
				getLoopInterpolants(mCounterexample.getLoop(), hondaPredicate, rankEqAndSi, pu);

		// TODO: see if the predicate unifier messes with this
		final IHoareTripleChecker ehtc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
		// hoare triple checker that can handle the oldrank/ranking function stuff
		final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
		bhtc.putDecreaseEqualPair(hondaPredicate, rankEqAndSi);

//-------------------------- merge prevention --------------------------------------------------------------------------

		final NestedWord<L> stemWord = mCounterexample.getStem().getWord();
		// the hoare triple checks and a lot of other things only work with the unified predicates from the pu, so we
		// have to keep them in some form
		final HashMap<IPredicate, IPredicate> correspUnifiedPred = new HashMap<>();

		// TODO: code this properly
		final IPredicate[] stemInterpolants = new IPredicate[unifiedStemInterpolants.length];
		for (int i = 0; i < unifiedStemInterpolants.length; i++) {
			correspUnifiedPred.putIfAbsent(unifiedStemInterpolants[i], unifiedStemInterpolants[i]);
			stemInterpolants[i] = unifiedStemInterpolants[i];

		}

		if (unifiedStemInterpolants.length > 2) {
			for (int i = 0; i < unifiedStemInterpolants.length - 1; i++) {
				if (unifiedStemInterpolants[i] == unifiedStemInterpolants[i + 1]) {
					// we may only merge states with no non-loop edge inbetween
					final L sepSt = stemWord.getSymbol(i + 1);
					if (!unfairRes.loopThreads().contains(stemWord.getSymbol(i + 1).getSource().getProcedure())) {
						stemInterpolants[i] = mPredicateFactory.newPredicate(unifiedStemInterpolants[i].getFormula());
						correspUnifiedPred.put(stemInterpolants[i], unifiedStemInterpolants[i]);

					}
				}
			}
		}

		// hondaPrime is supposed to be the state after the assume notG edge in A_fair
		IPredicate hondaPrime = mPredicateFactory.newPredicate(unfairRes.notG().getFormula());
		hondaPrime = mPredicateFactory.and(hondaPredicate, hondaPrime);

		// get the predicates on the upper loop
		final InterpolatingTraceCheck<L> upperLoopCheck =
				constructTraceCheck(hondaPredicate, hondaPredicate, mCounterexample.getLoop(), pu);
		final IPredicate[] upperLoopInterpolants = upperLoopCheck.getInterpolants();

		// get the predicates on the lower loop
		final InterpolatingTraceCheck<L> guardedLoopCheck =
				constructTraceCheck(hondaPrime, hondaPredicate, mCounterexample.getLoop(), pu);
		final IPredicate[] guardedLoopInterpolants = guardedLoopCheck.getInterpolants();

		final IPredicate[] loopInterpolants = new IPredicate[unifiedLoopInterpolants.length];
		// loop -->(upper loop, guarded loop); since the loop interpolants are supposed to be unique this should be ok
		// TODO: check if the honda is mapped properly
		final HashMap<IPredicate, Pair<IPredicate, IPredicate>> loopMap = new HashMap<>();

		for (int i = 0; i < unifiedLoopInterpolants.length; i++) {
			loopInterpolants[i] = unifiedLoopInterpolants[i];
			correspUnifiedPred.putIfAbsent(unifiedLoopInterpolants[i], unifiedLoopInterpolants[i]);
			loopMap.putIfAbsent(loopInterpolants[i], new Pair<>(upperLoopInterpolants[i], guardedLoopInterpolants[i]));
		}
		if (unifiedLoopInterpolants.length > 2) {
			for (int i = 1; i < unifiedLoopInterpolants.length; i++) {
				// we are only allowed to merge if the predicates of adjacent states are the same on the upper and on
				// the lower loop
				// TODO: for debugging only, remove superfluous vars once done
				final boolean u = unifiedLoopInterpolants[i - 1] == unifiedLoopInterpolants[i];
				if (u) {
					final boolean upper = upperLoopInterpolants[i - 1] == upperLoopInterpolants[i];
					final boolean guarded = guardedLoopInterpolants[i - 1] == guardedLoopInterpolants[i];
					if (!(upper && guarded)) {
						loopInterpolants[i] = mPredicateFactory.newPredicate(unifiedLoopInterpolants[i].getFormula());
						loopMap.putIfAbsent(loopInterpolants[i],
								new Pair<>(upperLoopInterpolants[i], guardedLoopInterpolants[i]));
					}

				}
			}
		}
//------------------------------------------ merge prevention end ---------------------------------------------

		final Set<IPredicate> stemSet = new HashSet<>(Arrays.asList(stemInterpolants));
		final Set<IPredicate> loopSet = new HashSet<>(Arrays.asList(loopInterpolants));

		final List<IPredicate> stateSeq = new ArrayList();
		stateSeq.add(hondaPrime);
		stateSeq.addAll(mCounterexample.getLoop().getStateSequence());

//----------------------------------------------------------------------------------------------------------------------
		// Warning: the interpolant automaton already merges states with the same predicate! - and because of the
		// predicate unifier, all predicates with the same formula count as the same predicate

		final NestedWordAutomaton<L, IPredicate> inputAutomaton =
				mInterpolantAutomatonBuilder.constructInterpolantAutomaton(unfairRes.result().getStemPrecondition(),
						mCounterexample, stemInterpolants, hondaPredicate, loopInterpolants,
						BuchiAutomizerUtils.getVpAlphabet(mAbstraction), mDefaultStateFactory);
		// when constructing an interpolant automaton, an initial state is added
		for (final IPredicate init : inputAutomaton.getInitialStates()) {
			correspUnifiedPred.put(init, init);
			stemSet.add(init);
		}

		// TODO: check if this does what I think it does
		final NestedMap3<IPredicate, L, IPredicate, IsContained> originalEdges = inputAutomaton.mInternalOut;

		// TODO: Can/should we do an equivalent check for the unfair automaton?
		/*
		 * assert NwaFloydHoareValidityCheck.forInterpolantAutomaton(mServices,
		 * mCsToolkitWithRankVars.getManagedScript(), bhtc, pu, inputAutomaton, true,
		 * unfairRes.result().getStemPrecondition()).getResult();
		 */
		// TODO: figure out how to do buchi accepts with ununified predicates
		// assert new BuchiAccepts<>(new AutomataLibraryServices(mServices),
		// inputAutomaton,mCounterexample.getNestedLassoWord()).getResult();

		// the equivalent to constructGeneralizedAutomaton, but we always do nondeterminism
		if (!inputAutomaton.getStates().contains(pu.getTruePredicate())) {
			inputAutomaton.addState(false, false, pu.getTruePredicate());
		}
		if (!inputAutomaton.getStates().contains(pu.getFalsePredicate())) {
			inputAutomaton.addState(false, true, pu.getFalsePredicate());
		}

		final ReplacingBuchiHoareTripleChecker rbhtc =
				new ReplacingBuchiHoareTripleChecker(new BuchiHoareTripleChecker(ehtc), correspUnifiedPred);

		// automaton generalized under terminationrules
		final NondeterministicInterpolantAutomaton<L> tbwAutomaton = new NondeterministicInterpolantAutomaton<>(
				mServices, mCsToolkitWithRankVars, rbhtc, inputAutomaton, pu, false, true, true, correspUnifiedPred);

		// TODO: if we want fair termination, wrap the interpolant automaton to filter out transitions that may lead to
		// fair runs
		final FairnessWrapper<L> generalizedAutomaton = new FairnessWrapper<>(tbwAutomaton, unfairRes.loopThreads(),
				originalEdges, stemSet, loopSet, loopMap, hondaPredicate, unfairRes.notG(), rbhtc);

		// disabled bc the it doesnt work with ununified predicates -.-
		/*
		 * assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), tbwAutomaton,
		 * mCounterexample.getNestedLassoWord()).getResult() :
		 * "the generalized automaton does not accept the original trace";
		 */
		// TODO: can we properly compute the difference when we use un-unified predicates?
		newAbstr = refineBuchi(mAbstraction, generalizedAutomaton);
		// Switch to read-only-mode for lazy constructions
		// inputAutomaton.switchToReadonlyMode();

		mBenchmarkGenerator.addEdgeCheckerData(bhtc.getStatistics());

		/*
		 * final boolean isUseful = isUsefulInterpolantAutomaton(generalizedAutomaton, mCounterexample); if (isUseful) {
		 * mMDBenchmark.reportNonDeterministicModule(mIteration, generalizedAutomaton.size()); }
		 */
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		mBenchmarkGenerator.addBackwardCoveringInformationBuchi(mBci);
		return newAbstr;
	}

	private A refineBuchiInternal(final BspmResult bspmResult) throws AutomataOperationCanceledException {
		final IPredicate hondaPredicate = bspmResult.getHondaPredicate();
		final IPredicate rankEqAndSi = bspmResult.getRankEqAndSi();

		assert !SmtUtils.isFalseLiteral(bspmResult.getStemPrecondition().getFormula());
		assert !SmtUtils.isFalseLiteral(hondaPredicate.getFormula());
		assert !SmtUtils.isFalseLiteral(rankEqAndSi.getFormula());

		final boolean dumpAutomata = mPref.dumpAutomata();
		final String dumpPath = mPref.dumpPath();
		final Format format = mPref.getAutomataFormat();

		final RankingFunction rankingFunction = bspmResult.getTerminationArgument().getRankingFunction();
		final Script script = mCsToolkitWithRankVars.getManagedScript().getScript();
		mMDBenchmark.reportRankingFunction(mIteration, rankingFunction, script);

		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		int stage = 0;
		/*
		 * Iterate through a sequence of BuchiInterpolantAutomatonConstructionStyles Each construction style defines how
		 * an interpolant automaton is constructed. Constructions that provide simpler (less nondeterministic) automata
		 * should come first. In each iteration we compute the difference which causes an on-demand construction of the
		 * automaton and evaluate the automaton afterwards. If the automaton is "good" we keep the difference and
		 * continued with the termination analysis. If the automaton is "bad" we construct the next automaton. Currently
		 * an automaton is "good" iff the counterexample of the current CEGAR iteration is accepted by the automaton
		 * (otherwise the counterexample would not be excluded and we might get it again in the next iteration of the
		 * CEGAR loop).
		 *
		 */
		for (final BuchiInterpolantAutomatonConstructionStyle constructionStyle : mBiaConstructionStyleSequence) {
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton;
			A newAbstraction;
			boolean isUseful;
			try {
				final PredicateUnifier pu =
						new PredicateUnifier(mLogger, mServices, mCsToolkitWithRankVars.getManagedScript(),
								mPredicateFactory, mCsToolkitWithRankVars.getSymbolTable(), SIMPLIFICATION_TECHNIQUE,
								bspmResult.getStemPrecondition(), hondaPredicate, rankEqAndSi,
								bspmResult.getStemPostcondition(), bspmResult.getRankDecreaseAndBound(),
								bspmResult.getSiConjunction());
				final IPredicate[] stemInterpolants = getStemInterpolants(mCounterexample.getStem(),
						bspmResult.getStemPrecondition(), bspmResult.getStemPostcondition(), pu);
				final IPredicate[] loopInterpolants =
						getLoopInterpolants(mCounterexample.getLoop(), hondaPredicate, rankEqAndSi, pu);
				// input automaton : lasso module (automaton recognizing only the lasso trace)
				final NestedWordAutomaton<L, IPredicate> inputAutomaton =
						mInterpolantAutomatonBuilder.constructInterpolantAutomaton(bspmResult.getStemPrecondition(),
								mCounterexample, stemInterpolants, hondaPredicate, loopInterpolants,
								BuchiAutomizerUtils.getVpAlphabet(mAbstraction), mDefaultStateFactory);
				if (dumpAutomata) {
					final String filename = mIdentifier + "_" + "InterpolantAutomatonBuchi" + mIteration;
					BuchiAutomizerUtils.writeAutomatonToFile(mServices, inputAutomaton, dumpPath, filename, format,
							constructionStyle.toString());
				}
				final IHoareTripleChecker ehtc =
						HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
								HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
				final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
				bhtc.putDecreaseEqualPair(hondaPredicate, rankEqAndSi);
				assert NwaFloydHoareValidityCheck
						.forInterpolantAutomaton(mServices, mCsToolkitWithRankVars.getManagedScript(), bhtc, pu,
								inputAutomaton, true, bspmResult.getStemPrecondition())
						.getResult();

				assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), inputAutomaton,
						mCounterexample.getNestedLassoWord()).getResult();
				// V - this one should be the cert. module obtained from the current lasso trace

				interpolantAutomaton = mInterpolantAutomatonBuilder.constructGeneralizedAutomaton(mCounterexample,
						constructionStyle, bspmResult, pu, stemInterpolants, loopInterpolants, inputAutomaton, bhtc);
				mIsSemiDeterministic = constructionStyle.isAlwaysSemiDeterministic();
				// TODO: if we want fair termination, wrap the interpolant automaton for filtering
				newAbstraction = refineBuchi(mAbstraction, interpolantAutomaton);
				// Switch to read-only-mode for lazy constructions
				if (interpolantAutomaton instanceof NondeterministicInterpolantAutomaton) {
					((NondeterministicInterpolantAutomaton<?>) interpolantAutomaton).switchToReadonlyMode();
				} else if (interpolantAutomaton instanceof BuchiInterpolantAutomatonBouncer) {
					((BuchiInterpolantAutomatonBouncer<?>) interpolantAutomaton).switchToReadonlyMode();
				}
				mBenchmarkGenerator.addEdgeCheckerData(bhtc.getStatistics());
				isUseful = isUsefulInterpolantAutomaton(interpolantAutomaton, mCounterexample);
			} catch (final AutomataOperationCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "applying stage " + stage);
				throw new ToolchainCanceledException(e, rti);
			} catch (final ToolchainCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				throw e;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e.getMessage());
			}
			if (dumpAutomata) {
				final String automatonString;
				if (interpolantAutomaton.getVpAlphabet().getCallAlphabet().isEmpty()) {
					automatonString = "interpolBuchiAutomatonUsedInRefinement";
				} else {
					automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
				}
				final String filename = mIdentifier + "_" + automatonString + mIteration + "after";
				BuchiAutomizerUtils.writeAutomatonToFile(mServices, interpolantAutomaton, dumpPath, filename, format,
						constructionStyle.toString());
			}
			final boolean tacasDump = false;
			if (tacasDump) {
				final String determinicity;
				final boolean isSemiDeterministic =
						new IsSemiDeterministic<>(new AutomataLibraryServices(mServices), interpolantAutomaton)
								.getResult();
				final boolean isDeterministic =
						new IsDeterministic<>(new AutomataLibraryServices(mServices), interpolantAutomaton).getResult();
				if (isDeterministic) {
					determinicity = "deterministic";
					assert isSemiDeterministic : "but semi deterministic";
				} else if (isSemiDeterministic) {
					determinicity = "semideterministic";
				} else {
					determinicity = "nondeterministic";
				}
				final String automatonString;
				if (interpolantAutomaton.getVpAlphabet().getCallAlphabet().isEmpty()) {
					automatonString = "interpolBuchiAutomatonUsedInRefinement";
				} else {
					automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
				}
				final String filename = mIdentifier + "_" + determinicity + automatonString + mIteration + "after";
				BuchiAutomizerUtils.writeAutomatonToFile(mServices, interpolantAutomaton, dumpPath, filename, format,
						constructionStyle.toString());

			}
			if (isUseful) {
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportBuchiModule(mIteration, interpolantAutomaton);
				}
				mBenchmarkGenerator.announceSuccessfullRefinementStage(stage);
				switch (constructionStyle.getInterpolantAutomaton()) {
				case DETERMINISTIC:
				case LASSO_AUTOMATON:
					mMDBenchmark.reportDeterministicModule(mIteration, interpolantAutomaton.size());
					break;
				case SCROOGE_NONDETERMINISM:
				case EAGER_NONDETERMINISM:
					mMDBenchmark.reportNonDeterministicModule(mIteration, interpolantAutomaton.size());
					break;
				default:
					throw new AssertionError("unsupported");
				}
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				mBenchmarkGenerator.addBackwardCoveringInformationBuchi(mBci);
				return reduceAbstractionSize(newAbstraction, mAutomataMinimizationAfterRankBasedRefinement);
			}
			stage++;
		}
		throw new AssertionError("no settings was sufficient");
	}

	private boolean isUsefulInterpolantAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolAutomatonUsed,
			final NestedLassoRun<L, IPredicate> counterexample) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> oldApi;
		oldApi = new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolAutomatonUsed).getResult();
		final NestedWord<L> stem = counterexample.getStem().getWord();
		final NestedWord<L> loop = counterexample.getLoop().getWord();
		final NestedWord<L> stemAndLoop = stem.concatenate(loop);
		final NestedLassoWord<L> stemExtension = new NestedLassoWord<>(stemAndLoop, loop);
		final NestedWord<L> loopAndLoop = loop.concatenate(loop);
		final NestedLassoWord<L> loopExtension = new NestedLassoWord<>(stem, loopAndLoop);
		final boolean wordAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, counterexample.getNestedLassoWord())
						.getResult();
		if (!wordAccepted) {
			mLogger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		// 2015-01-14 Matthias: word, stemExtension, and loopExtension are only
		// different representations of the same word. The following lines
		// do not make any sense (but might be helpful to reveal a bug.
		final boolean stemExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, stemExtension).getResult();
		if (!stemExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: stem extension not accepted");
		}
		final boolean loopExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, loopExtension).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
		}
		return true;
	}

	private IPredicate[] getStemInterpolants(final NestedRun<L, IPredicate> stem, final IPredicate precondition,
			final IPredicate postcondition, final PredicateUnifier predicateUnifier) {
		if (BuchiAutomizerUtils.isEmptyStem(stem)) {
			return null;
		}
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(precondition, postcondition, stem, predicateUnifier);
		if (traceCheck.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - stem");
		}
		return traceCheck.getInterpolants();
	}

	/**
	 * Note: the number of interpolants is the length of the trace - 1
	 *
	 * @param rankEqAndSi
	 *            - precondition for the loop
	 *
	 * @param hondaPredicate
	 *            - postcondition
	 *
	 */
	private IPredicate[] getLoopInterpolants(final NestedRun<L, IPredicate> loop, final IPredicate hondaPredicate,
			final IPredicate rankEqAndSi, final PredicateUnifier predicateUnifier) {
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(rankEqAndSi, hondaPredicate, loop, predicateUnifier);
		// TODO: can this work if the loop is infeasible? should we give a trivial postcondition?
		if (traceCheck.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - loop");
		}
		mBci = TraceCheckUtils.computeCoverageCapability(mServices, traceCheck, mLogger);
		return traceCheck.getInterpolants();
	}

	private InterpolatingTraceCheck<L> constructTraceCheck(final IPredicate precond, final IPredicate postcond,
			final NestedRun<L, IPredicate> run, final PredicateUnifier predicateUnifier) {
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			return new InterpolatingTraceCheckCraig<>(precond, postcond, new TreeMap<>(),
					new Counterexample<>(run.getWord()), mServices, mCsToolkitWithRankVars, mPredicateFactory,
					predicateUnifier, AssertCodeBlockOrder.NOT_INCREMENTALLY, false, false, mInterpolation, true,
					SIMPLIFICATION_TECHNIQUE);
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect: {
			return new TraceCheckSpWp<>(precond, postcond, new TreeMap<>(), new Counterexample<>(run.getWord()),
					mCsToolkitWithRankVars, AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true,
					mServices, false, mPredicateFactory, predicateUnifier, mInterpolation,
					mCsToolkitWithRankVars.getManagedScript(), SIMPLIFICATION_TECHNIQUE, false);
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
	}

	private void reportRemainderModule(final boolean nonterminationKnown) {
		mMDBenchmark.reportRemainderModule(mAbstraction.size(), nonterminationKnown);
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportRemainderModule(nonterminationKnown);
		}
	}

	private HashRelation<String, ILocation> getOverapproximations() {
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();
		final HashRelation<String, ILocation> overapproximations = new HashRelation<>();
		overapproximations.addAll(Overapprox.getOverapproximations(stem.asList()));
		overapproximations.addAll(Overapprox.getOverapproximations(loop.asList()));
		return overapproximations;
	}

	protected Object getControlConfiguration(final IPredicate predicate) {
		if (mIsConcurrent) {
			return ((IMLPredicate) predicate).getProgramPoints();
		}
		return ((ISLPredicate) predicate).getProgramPoint();
	}

	private static class SubtaskAdditionalLoopUnwinding extends TaskIdentifier {
		private final int mAdditionaUnwindings;

		public SubtaskAdditionalLoopUnwinding(final TaskIdentifier parentTaskIdentifier,
				final int additionaUnwindings) {
			super(parentTaskIdentifier);
			mAdditionaUnwindings = additionaUnwindings;
		}

		@Override
		protected String getSubtaskIdentifier() {
			return mAdditionaUnwindings + "additionalUnwindings";
		}

	}
}
