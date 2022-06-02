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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
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

	protected final InterpolationTechnique mInterpolation;

	private final CfgSmtToolkit mCsToolkitWithoutRankVars;

	private final PredicateFactory mPredicateFactory;

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
	 * Refine the given {@code abstraction} (i.e. calculate the difference with some automaton) w.r.t.
	 * {@code lassoCheck} for the case where we detected that the lasso can only be taken finitely often.
	 *
	 * @param abstraction
	 *            The abstraction to be refined
	 * @param lassoCheck
	 *            The lasso check for the infeasible lasso
	 * @return The new refined abstraction
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract A refineBuchi(A abstraction, final LassoCheck<L> lassoCheck)
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
					mAbstraction = refineFiniteInternal(refineBuchiAndReportRankingFunction(lassoCheck), lassoCheck);
					break;
				case REFINE_FINITE:
					mAbstraction = refineFiniteInternal(mAbstraction, lassoCheck);
					break;
				case REFINE_BUCHI:
					mAbstraction = refineBuchiAndReportRankingFunction(lassoCheck);
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
			result = refineFinite(abstraction, determinized);
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

	private A refineBuchiAndReportRankingFunction(final LassoCheck<L> lassoCheck)
			throws AutomataOperationCanceledException {
		final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
		final ISLPredicate hondaISLP = (ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0);
		final IcfgLocation hondaPP = hondaISLP.getProgramPoint();
		mMDBenchmark.reportRankingFunction(mIteration, constructTAResult(bspm.getTerminationArgument(), hondaPP));

		final A result = refineBuchi(mAbstraction, lassoCheck);
		mBinaryStatePredicateManager.clearPredicates();
		return result;
	}

	private TerminationArgumentResult<IIcfgElement, Term>
			constructTAResult(final TerminationArgument terminationArgument, final IcfgLocation honda) {
		final RankingFunction rf = terminationArgument.getRankingFunction();
		final Term[] supportingInvariants = terminationArgument.getSupportingInvariants().stream()
				.map(si -> si.asTerm(mCsToolkitWithRankVars.getManagedScript().getScript())).toArray(Term[]::new);
		return new TerminationArgumentResult<>(honda, Activator.PLUGIN_NAME,
				rf.asLexTerm(mCsToolkitWithRankVars.getManagedScript().getScript()), rf.getName(), supportingInvariants,
				mServices.getBacktranslationService(), Term.class);
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
