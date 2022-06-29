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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
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
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBouncer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStyle;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class AbstractBuchiCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {

	/**
	 * Result of CEGAR loop iteration
	 * <ul>
	 * <li>SAFE: there is no feasible trace to an error location
	 * <li>UNSAFE: there is a feasible trace to an error location (the underlying program has at least one execution
	 * which violates its specification)
	 * <li>UNKNOWN: we found a trace for which we could not decide feasibility or we found an infeasible trace but were
	 * not able to exclude it in abstraction refinement.
	 * <li>TIMEOUT:
	 */
	public enum Result {
		TERMINATING, TIMEOUT, UNKNOWN, NONTERMINATING
	}

	protected static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	protected static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected final String mIdentifier;
	protected final CfgSmtToolkit mCsToolkitWithRankVars;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected NestedLassoRun<L, IPredicate> mCounterexample;

	protected final PredicateFactoryForInterpolantAutomata mDefaultStateFactory;

	protected final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;

	protected final BuchiCegarLoopBenchmarkGenerator mBenchmarkGenerator;

	/**
	 * Construct a termination proof in the form that is required for the Termination Competition.
	 * http://termination-portal.org/wiki/Termination_Competition This proof is finally print in the console output and
	 * can be huge.
	 */
	protected final boolean mConstructTermcompProof;
	protected final TermcompProofBenchmark mTermcompProofBenchmark;

	private final InterpolationTechnique mInterpolation;

	protected final PredicateFactory mPredicateFactory;

	private BackwardCoveringInformation mBci;

	private final CfgSmtToolkit mCsToolkitWithoutRankVars;

	private final BinaryStatePredicateManager mBinaryStatePredicateManager;
	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of of the program.
	 */
	private A mAbstraction;

	private NonTerminationArgument mNonterminationArgument;

	private ToolchainCanceledException mToolchainCancelledException;

	private final StrategyFactory<L> mRefinementStrategyFactory;
	private final TaskIdentifier mTaskIdentifier;
	private final BuchiInterpolantAutomatonBuilder<L> mInterpolantAutomatonBuilder;
	private final List<BuchiInterpolantAutomatonConstructionStyle> mBiaConstructionStyleSequence;
	private final Minimization mAutomataMinimizationAfterFeasbilityBasedRefinement;
	private final Minimization mAutomataMinimizationAfterRankBasedRefinement;
	protected boolean mIsSemiDeterministic;

	public AbstractBuchiCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz, final A initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		assert services != null;
		mIdentifier = icfg.getIdentifier();
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIdentifier);
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
				predicateFactory, mPref.computeHoareAnnotation());

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mInterpolation = baPref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);

		InterpolationPreferenceChecker.check(Activator.PLUGIN_NAME, mInterpolation, mServices);
		mConstructTermcompProof = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		mTermcompProofBenchmark = mConstructTermcompProof ? new TermcompProofBenchmark(mServices) : null;

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, SIMPLIFICATION_TECHNIQUE,
						XNF_CONVERSION_TECHNIQUE, mCsToolkitWithoutRankVars, mPredicateFactory, icfg);
		mRefinementStrategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs, icfg,
				mPredicateFactory, mDefaultStateFactory, transitionClazz);
		mAbstraction = initialAbstraction;
		mInterpolantAutomatonBuilder = new BuchiInterpolantAutomatonBuilder<>(mServices, mCsToolkitWithRankVars,
				SIMPLIFICATION_TECHNIQUE, XNF_CONVERSION_TECHNIQUE, predicateFactory, mDefaultStateFactory);
		mBiaConstructionStyleSequence =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
						BuchiInterpolantAutomatonConstructionStrategy.class).getBiaConstrucionStyleSequence(baPref);
		mAutomataMinimizationAfterFeasbilityBasedRefinement = baPref.getEnum(
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
	 *            The current abstract
	 * @return true iff {@code abstraction} is empty
	 * @throws AutomataLibraryException
	 */
	protected abstract boolean isAbstractionEmpty(A abstraction) throws AutomataLibraryException;

	/**
	 * Refine the given {@code abstraction} (i.e. calculate the difference with some automaton) for the case where we
	 * detected that a finite prefix of the lasso-shaped counterexample is infeasible. In this case the module (i.e.,
	 * the subtrahend {@code interpolantAutomaton} of the difference) will be a weak Büchi automaton (Büchi automaton
	 * where set of final states is a trap). In fact, the module will have only a single accepting state that is labeled
	 * with "false" and that has a self-loop for every letter.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param interpolantAutomaton
	 *            The automaton check for the infeasible lasso
	 * @return The new refined abstraction
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A refineFinite(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataOperationCanceledException;

	/**
	 * Refine the given {@code abstraction} (i.e. calculate the difference with some automaton) w.r.t. {@code bspm} for
	 * the case where we detected that the lasso can only be taken finitely often.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param bspm
	 *            The {@code BinaryStatePredicateManager} representing the infeasible lasso
	 * @return The new refined abstraction
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A refineBuchi(A abstraction,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException;

	protected abstract A reduceAbstractionSize(final A abstraction, final Minimization automataMinimization)
			throws AutomataOperationCanceledException;

	public NestedLassoRun<L, IPredicate> getCounterexample() {
		return mCounterexample;
	}

	public final Result runCegarLoop() throws IOException {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.computeHoareAnnotation());
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
			mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
			return Result.TIMEOUT;
		}
		if (initalAbstractionCorrect) {
			mMDBenchmark.reportNoRemainderModule();
			return Result.TERMINATING;
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
				mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
				return Result.TIMEOUT;
			}
			if (abstractionCorrect) {
				mMDBenchmark.reportNoRemainderModule();
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportNoRemainderModule();
				}
				return Result.TERMINATING;
			}

			LassoCheck<L> lassoCheck;
			try {
				final TaskIdentifier taskIdentifier = new SubtaskIterationIdentifier(mTaskIdentifier, mIteration);
				mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
				lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
						mCsToolkitWithoutRankVars.getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
						mCounterexample, generateLassoCheckIdentifier(), mServices, SIMPLIFICATION_TECHNIQUE,
						XNF_CONVERSION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction, taskIdentifier,
						mBenchmarkGenerator);
				if (lassoCheck.getLassoCheckResult().getContinueDirective() == ContinueDirective.REPORT_UNKNOWN) {
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
							mCounterexample, generateLassoCheckIdentifier(), mServices, SIMPLIFICATION_TECHNIQUE,
							XNF_CONVERSION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction, unwindingTaskIdentifier,
							mBenchmarkGenerator);
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
				mToolchainCancelledException = e;
				return Result.TIMEOUT;
			} finally {
				mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
			}

			final ContinueDirective cd = lassoCheck.getLassoCheckResult().getContinueDirective();
			mBenchmarkGenerator.reportLassoAnalysis(lassoCheck);
			try {
				switch (cd) {
				case REFINE_BOTH:
					mAbstraction = refineFiniteInternal(refineBuchiInternal(lassoCheck), lassoCheck);
					break;
				case REFINE_FINITE:
					mAbstraction = refineFiniteInternal(mAbstraction, lassoCheck);
					break;
				case REFINE_BUCHI:
					mAbstraction = refineBuchiInternal(lassoCheck);
					break;
				case REPORT_UNKNOWN:
					reportRemainderModule(false);
					return Result.UNKNOWN;
				case REPORT_NONTERMINATION:
					if (getOverapproximations().isEmpty()) {
						mNonterminationArgument = lassoCheck.getNonTerminationArgument();
						reportRemainderModule(true);
						return Result.NONTERMINATING;
					}
					reportRemainderModule(false);
					return Result.UNKNOWN;
				default:
					throw new AssertionError("impossible case");
				}
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());

				if (mPref.dumpAutomata()) {
					final String filename = mIdentifier + "_" + name + "Abstraction" + mIteration;
					BuchiAutomizerUtils.writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
							mPref.getAutomataFormat(), "");
				}

			} catch (final AutomataOperationCanceledException e) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "performing iteration " + mIteration);
				mToolchainCancelledException = new ToolchainCanceledException(e, rti);
				return Result.TIMEOUT;
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				return Result.TIMEOUT;
			}
		}
		return Result.TIMEOUT;
	}

	private A refineFiniteInternal(final A abstraction, final LassoCheck<L> lassoCheck)
			throws AutomataOperationCanceledException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> traceCheck;
		final LassoCheck<L>.LassoCheckResult lcr = lassoCheck.getLassoCheckResult();
		if (lassoCheck.getLassoCheckResult().getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			// if both (stem and loop) are infeasible we take the smaller one.
			final int stemSize = mCounterexample.getStem().getLength();
			final int loopSize = mCounterexample.getLoop().getLength();
			if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE && loopSize <= stemSize) {
				traceCheck = lassoCheck.getLoopCheck();
			} else {
				traceCheck = lassoCheck.getStemCheck();
			}
		} else if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
			traceCheck = lassoCheck.getLoopCheck();
		} else {
			assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
			traceCheck = lassoCheck.getConcatCheck();
		}

		final NestedWordAutomaton<L, IPredicate> interpolAutomaton = traceCheck.getInfeasibilityProof();

		final IHoareTripleChecker htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, traceCheck.getPredicateUnifier());

		final DeterministicInterpolantAutomaton<L> determinized = new DeterministicInterpolantAutomaton<>(mServices,
				mCsToolkitWithRankVars, htc, interpolAutomaton, traceCheck.getPredicateUnifier(), false, false);
		final A result;
		try {
			result = reduceAbstractionSize(refineFinite(abstraction, determinized),
					mAutomataMinimizationAfterFeasbilityBasedRefinement);
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
		assert new InductivityCheck<>(mServices, interpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mCsToolkitWithRankVars, false)).getResult();
		mBenchmarkGenerator.addEdgeCheckerData(htc.getStatistics());
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		return result;
	}

	private A refineBuchiInternal(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
		assert !SmtUtils.isFalseLiteral(bspm.getStemPrecondition().getFormula());
		assert !SmtUtils.isFalseLiteral(bspm.getHondaPredicate().getFormula());
		assert !SmtUtils.isFalseLiteral(bspm.getRankEqAndSi().getFormula());

		final boolean dumpAutomata = mPref.dumpAutomata();
		final String dumpPath = mPref.dumpPath();
		final Format format = mPref.getAutomataFormat();

		final RankingFunction rankingFunction = bspm.getTerminationArgument().getRankingFunction();
		final Script script = mCsToolkitWithRankVars.getManagedScript().getScript();
		mMDBenchmark.reportRankingFunction(mIteration, rankingFunction, script);

		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		int stage = 0;
		// final BuchiModGlobalVarManager bmgvm = new BuchiModGlobalVarManager(
		// lassoChecker.getBinaryStatePredicateManager().getUnseededVariable(),
		// lassoChecker.getBinaryStatePredicateManager().getOldRankVariables(),
		// mRootAnnot.getCfgSmtToolkit().getModifiableGlobals(), mRootAnnot.getBoogie2SMT());

		/*
		 * Iterate through a sequence of BuchiInterpolantAutomatonConstructionStyles Each construction style defines how
		 * an interpolant automaton is constructed. Constructions that provide simpler (less nondeterministic) automata
		 * should come first. In each iteration we compute the difference which causes an on-demand construciton of the
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
				final PredicateUnifier pu = new PredicateUnifier(mLogger, mServices,
						mCsToolkitWithRankVars.getManagedScript(), mPredicateFactory,
						mCsToolkitWithRankVars.getSymbolTable(), SIMPLIFICATION_TECHNIQUE, XNF_CONVERSION_TECHNIQUE,
						bspm.getStemPrecondition(), bspm.getHondaPredicate(), bspm.getRankEqAndSi(),
						bspm.getStemPostcondition(), bspm.getRankDecreaseAndBound(), bspm.getSiConjunction());
				final IPredicate[] stemInterpolants = getStemInterpolants(mCounterexample.getStem(), bspm, pu);
				final IPredicate[] loopInterpolants = getLoopInterpolants(mCounterexample.getLoop(), bspm, pu);
				final NestedWordAutomaton<L, IPredicate> tmpAutomaton =
						mInterpolantAutomatonBuilder.constructInterpolantAutomaton(bspm.getStemPrecondition(),
								mCounterexample, stemInterpolants, bspm.getHondaPredicate(), loopInterpolants,
								BuchiAutomizerUtils.getVpAlphabet(mAbstraction), mDefaultStateFactory);
				if (dumpAutomata) {
					final String filename = mIdentifier + "_" + "InterpolantAutomatonBuchi" + mIteration;
					BuchiAutomizerUtils.writeAutomatonToFile(mServices, tmpAutomaton, dumpPath, filename, format,
							constructionStyle.toString());
				}
				final IHoareTripleChecker ehtc =
						HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
								HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
				final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
				bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
				assert new InductivityCheck<>(mServices, tmpAutomaton, false, true, bhtc).getResult();
				assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), tmpAutomaton,
						mCounterexample.getNestedLassoWord()).getResult();

				interpolantAutomaton =
						mInterpolantAutomatonBuilder.constructGeneralizedAutomaton(mCounterexample, constructionStyle,
								bspm, mInterpolation, pu, stemInterpolants, loopInterpolants, tmpAutomaton, bhtc);
				mIsSemiDeterministic = constructionStyle.isAlwaysSemiDeterministic();
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
				mBinaryStatePredicateManager.clearPredicates();
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

	private IPredicate[] getStemInterpolants(final NestedRun<L, IPredicate> stem,
			final BinaryStatePredicateManager bspm, final PredicateUnifier predicateUnifier) {
		if (BuchiAutomizerUtils.isEmptyStem(stem)) {
			return null;
		}
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(bspm.getStemPrecondition(), bspm.getStemPostcondition(), stem, predicateUnifier);
		if (traceCheck.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - stem");
		}
		return traceCheck.getInterpolants();
	}

	private IPredicate[] getLoopInterpolants(final NestedRun<L, IPredicate> loop,
			final BinaryStatePredicateManager bspm, final PredicateUnifier predicateUnifier) {
		final InterpolatingTraceCheck<L> traceCheck =
				constructTraceCheck(bspm.getRankEqAndSi(), bspm.getHondaPredicate(), loop, predicateUnifier);
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
			return new InterpolatingTraceCheckCraig<>(precond, postcond, new TreeMap<>(), run.getWord(), null,
					mServices, mCsToolkitWithRankVars, mPredicateFactory, predicateUnifier,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, false, false, mInterpolation, true,
					XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE);
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect: {
			return new TraceCheckSpWp<>(precond, postcond, new TreeMap<>(), run.getWord(), mCsToolkitWithRankVars,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, false,
					mPredicateFactory, predicateUnifier, mInterpolation, mCsToolkitWithRankVars.getManagedScript(),
					XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE, null, false);
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

	public Map<String, ILocation> getOverapproximations() {
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();
		final Map<String, ILocation> overapproximations = new HashMap<>();
		overapproximations.putAll(Overapprox.getOverapproximations(stem.asList()));
		overapproximations.putAll(Overapprox.getOverapproximations(loop.asList()));
		return overapproximations;
	}

	public ToolchainCanceledException getToolchainCancelledException() {
		return mToolchainCancelledException;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		return mNonterminationArgument;
	}

	public BuchiAutomizerModuleDecompositionBenchmark getMDBenchmark() {
		return mMDBenchmark;
	}

	public TermcompProofBenchmark getTermcompProofBenchmark() {
		return mTermcompProofBenchmark;
	}

	/**
	 * Returns an Identifier that describes a lasso analysis. Right now, this is the Filename (without path prefix) of
	 * analyzed file together with the number of the current iteration.
	 *
	 */
	private String generateLassoCheckIdentifier() {
		return mIdentifier + "_Iteration" + mIteration;
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
