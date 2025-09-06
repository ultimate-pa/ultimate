package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.Callable;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IpTcStrategyModuleAcceleratedTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.ParallelRefinementStrategy.WorkerGeneralizationMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class CegarNwaWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements Callable<WorkerThreadResult<L, A>> {

	private final ILogger mLogger;
	private final TAPreferences mPref;

	private final CegarLoopResultBuilder mResultBuilder;
	private final IUltimateServiceProvider mServices;

	// SMT solver warning
	private final CfgSmtToolkit mCsToolkit;
	final PredicateFactory mPredicateFactory;
	PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;

	// globally
	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	// each worker needs one of their own:
	private final int mIteration;
	private final IRun<L, ?> mCounterexample;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;

	// each worker needs one of their own, but creates it themself:
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult;
	private NestedWordAutomaton<L, IPredicate> mInterpolAutomaton;

	// contains SMT solver stuff, should be done by master anyway
	private final StrategyFactory<L> mStrategyFactory;

	// ???
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	boolean mComputeHoareAnnotation;

	private WorkerThreadResult<L, A> mThreadResult = null;
	BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;

	private final ITARefinementStrategy<L> mStrategy;
	private final IcfgLocation mCurrentErrorLoc;

	// for error automata
	private final boolean mUseGoalSetForIsEmpty;
	private final SimplificationTechnique mSimplificationTechnique;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	// Globals for Difference (Interpolant Automaton Enhancement)
	protected static final boolean REMOVE_DEAD_ENDS = true;
	private final ParallelNwaCegarLoop<L, A> mMainThread;

	private final WorkerGeneralizationMode mGeneralize;

	public CegarNwaWorkerThread(final ILogger logger, final TAPreferences pref, final IRun<L, ?> counterexample,
			final int iteration, final CegarLoopResultBuilder resultBuilder,
			final CegarLoopStatisticsGenerator statistcs, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final StrategyFactory<L> strategyFactory,
			final PredicateFactory predicateFactory,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ITARefinementStrategy<L> strategy, final IcfgLocation currentErrorLoc, final IIcfg<?> rootNode,
			final ParallelNwaCegarLoop<L, A> mainThread, final WorkerGeneralizationMode generalization,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults) {

		mLogger = logger;
		mPref = pref;
		mRefinementResult = null;
		mCounterexample = counterexample;
		mResultBuilder = resultBuilder;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mInterpolAutomaton = null;
		mIteration = iteration;
		mCegarLoopBenchmark = statistcs;
		mServices = services;
		mCsToolkit = csToolkit;
		mStrategyFactory = strategyFactory;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mStrategy = strategy;
		mCurrentErrorLoc = currentErrorLoc;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mIcfg = rootNode;
		mUseGoalSetForIsEmpty = pref.useGoalSetForIsEmpty;
		mMainThread = mainThread;
		mGeneralize = generalization;
		mBlockingQueueForResults = blockingQueueForResults;
	}

	@Override
	public WorkerThreadResult<L, A> call() throws InterruptedException {
		final List<L> trace = mCounterexample.getWord().asList();
		final int traceHash = trace.hashCode();
		mLogger.info("Starting Thread: " + Thread.currentThread().getId() + "# for Trace Check: " + traceHash);
		Thread.currentThread().setName("Worker for " + traceHash);
		try {
			final Pair<LBool, IProgramExecution<L, Term>> isCexResult = isCounterexampleFeasible(mStrategy);

			if (mUseGoalSetForIsEmpty && !isCexResult.getFirst().equals(LBool.UNSAT)) {
				// in this setting we dont use error automata
				mThreadResult =
						new WorkerThreadResult<>(null, null, null, false, null, false, AutomatonType.ERROR,
								mCsToolkit.getManagedScript(), mCounterexample, null, true, false, false);
				mBlockingQueueForResults.put(mThreadResult);
				return mThreadResult;
			}

			final AbstractCegarLoop.AutomatonType automatonType =
					processFeasibilityCheckResult(isCexResult.getFirst(), isCexResult.getSecond(), mCurrentErrorLoc);
			constructRefinementAutomaton(automatonType);
			mThreadResult = refineAbstractionInternally();
		} catch (AutomataLibraryException | ToolchainCanceledException e) {
			throw new AssertionError("WorkerThread Failed: " + e);
		}
		mLogger.info("Done with Thread: " + Thread.currentThread().getId() + "#");
		mBlockingQueueForResults.put(mThreadResult);
		return mThreadResult;
	}

	protected Pair<LBool, IProgramExecution<L, Term>>
			isCounterexampleFeasible(final ITARefinementStrategy<L> strategy) {
		IStatisticsDataProvider refinementEngineStats = null;
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount((Word<L>) mCounterexample)) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();
			refinementEngineStats = refinementEngine.getRefinementEngineStatistics();

		} catch (final ToolchainCanceledException tce) {
			throw tce;
		}
		final LBool feasibility = mRefinementResult.getCounterexampleFeasibility();
		IProgramExecution<L, Term> rcfgProgramExecution = null;
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample %s feasible", feasibility == LBool.SAT ? "is" : "might be");
			if (mRefinementResult.providesIcfgProgramExecution()) {
				rcfgProgramExecution = mRefinementResult.getIcfgProgramExecution();
			} else {
				rcfgProgramExecution =
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}

		}
		// leads to concurrency problems!
		// mCegarLoopBenchmark.addRefinementEngineStatistics(refinementEngineStats);
		return new Pair<>(feasibility, rcfgProgramExecution);
	}

	/**
	 * Report results from a feasibility check if necessary and return the type of the refinement automaton
	 */
	public AbstractCegarLoop.AutomatonType processFeasibilityCheckResult(final LBool isCounterexampleFeasible,
			final IProgramExecution<L, Term> programExecution, final IcfgLocation currentErrorLoc) {
		if (isCounterexampleFeasible == Script.LBool.SAT) {
			mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			}
			return AbstractCegarLoop.AutomatonType.ERROR;
		}
		if (isCounterexampleFeasible != Script.LBool.UNKNOWN) {
			return AbstractCegarLoop.AutomatonType.INTERPOLANT;
		}
		Result actualResult;
		if (programExecution != null) {
			for (final ITraceCheckStrategyModule<L, ?> module : mStrategy.getTraceCheckModules()) {
				if (module instanceof IpTcStrategyModuleAcceleratedTraceCheck) {
					throw new AssertionError(
							"TraceCheck Unknown, dont return result. Might be just this Strategy that fails");
				}
			}
			final UnprovabilityReason reasonUnknown =
					new UnprovabilityReason("unable to decide satisfiability of path constraint");
			actualResult = Result.UNKNOWN;
			mResultBuilder.addResultForProgramExecution(actualResult, programExecution, null, reasonUnknown);
		}
		actualResult = Result.TIMEOUT;
		mResultBuilder.addResult(currentErrorLoc, actualResult, null, null, null);

		if (mPref.stopAfterFirstViolation()) {
			mResultBuilder.addResultForAllRemaining(actualResult);
		}

		return AbstractCegarLoop.AutomatonType.UNKNOWN;
	}

	public void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType)
			throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			constructErrorAutomaton();
			break;
		case INTERPOLANT:
			constructInterpolantAutomaton();
			break;
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {

		mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
				mRefinementResult.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable(), mPredicateFactoryInterpolantAutomata,
				mMainThread.getAbstraction(), mIteration);
		mInterpolAutomaton = null;
		// for (final IPredicate testGoal : mMainThread.getAbstraction().getFinalStates()) {
		// final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
		// if (testGoalISL.getProgramPoint().getPayload().getAnnotations()
		// .containsKey(VarAssignmentReuseAnnotation.class.getName())) {
		//
		// final VarAssignmentReuseAnnotation pLocAnnoVA = (VarAssignmentReuseAnnotation) testGoalISL
		// .getProgramPoint().getPayload().getAnnotations()
		// .get(VarAssignmentReuseAnnotation.class.getName());
		// // If it contains a VA it should contain a TG
		// assert testGoalISL.getProgramPoint().getPayload().getAnnotations()
		// .containsKey(TestGoalAnnotation.class.getName());
		// final TestGoalAnnotation pLocAnnoTG = (TestGoalAnnotation) testGoalISL.getProgramPoint().getPayload()
		// .getAnnotations().get(TestGoalAnnotation.class.getName());
		//
		// // TODO
		// // if (!pLocAnnoVA.mIsActiveTestGoal || mTestGoalWorkingSet.contains(pLocAnnoTG.mId)) {
		// // mErrorGeneralizationEngine.addCoveredTestGoalToErrorAutomaton(testGoal,
		// // mAbstraction.internalPredecessors(testGoal));
		// // }
		//
		// }
		// }

		// TODO reactivate
		// final NestedWordAutomaton<L, IPredicate> resultBeforeEnhancement =
		// mErrorGeneralizationEngine.getResultBeforeEnhancement();
		// assert isInterpolantAutomatonOfSingleStateType(resultBeforeEnhancement);
		// assert accepts(getServices(), resultBeforeEnhancement, mCounterexample.getWord(),
		// false) : "Error automaton broken!";
	}

	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();

		// TODO reactivate checks NON_EA_INDUCTIVITY_CHECK and assert

		// assert isInterpolantAutomatonOfSingleStateType(mInterpolAutomaton);
		// if (NON_EA_INDUCTIVITY_CHECK) {
		// final boolean inductive = new InductivityCheck<>(getServices(), mInterpolAutomaton, false, true,
		// new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();
		//
		// if (!inductive) {
		// throw new AssertionError("not inductive");
		// }
		// }
		//
		// assert accepts(getServices(), mInterpolAutomaton, mCounterexample.getWord(),
		// false) : "Interpolant automaton broken!: " + mCounterexample.getWord() + " not accepted";
		//
		// assert new InductivityCheck<>(getServices(), mInterpolAutomaton, false, true,
		// new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	/*
	 * construct the subtrahend automaton
	 *
	 *
	 * Globals: mErrorGeneralizationEngine mIteration mStateFactoryForRefinement mRefinementResult mInterpolAutomaton
	 */
	public WorkerThreadResult<L, A> refineAbstractionInternally() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();

		final BasicCegarLoop.AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = BasicCegarLoop.AutomatonType.ERROR;
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		} else {
			automatonType = BasicCegarLoop.AutomatonType.FLOYD_HOARE;
			useErrorAutomaton = false;
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(enhanceMode, predicateUnifier, htc, subtrahendBeforeEnhancement);

		}

		// TODO: HTC and predicateunifier statistics are saved in the following
		// method, but it seems better to save them
		// at the end of the htc lifecycle instead of there

		if (generalize()) {
			mLogger.info("Difference in Worker for Generalization");
			computeAutomataDifference(mMainThread.getAbstraction(), subtrahend, subtrahendBeforeEnhancement,
					predicateUnifier, exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);
		}
		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(subtrahend, subtrahendBeforeEnhancement,
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCsToolkit.getManagedScript(), mCounterexample, mPredicateFactory,
				mRefinementResult.somePerfectSequenceFound(), false, false);

		// TODO missing a lot of stuff from NwaCegarLoop

		return workerResult;
	}

	private boolean generalize() {
		switch (mGeneralize) {
		case YES:
			return true;
		case NO:
			return false;
		case ONLYIFPERFECT:
			return mRefinementResult.somePerfectSequenceFound();
		default:
			throw new AssertionError("Unknown Worker Generalisation Mode");
		}
	}

	/*
	 * WARNING The real difference has to be computed in the Main Thrad / CEGAR loop This is only used to enhance the
	 * interpolant automaton
	 */
	private void computeAutomataDifference(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		if (automatonType.equals(AutomatonType.ERROR) || enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			return;
		}
		try {
			mLogger.debug("WORKER: Start constructing difference for enhancing interpolant automaton in worker");
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, explointSigmaStarConcatOfIA);
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(subtrahend.size());
			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				final RunningTaskInfo runningTaskInfo = executeDifferenceTimeoutActions(minuend, subtrahend,
						subtrahendBeforeEnhancement, automatonType);
				tce.addRunningTaskInfo(runningTaskInfo);
				throw tce;
			} finally {

				assert subtrahend instanceof AbstractInterpolantAutomaton
						: "if enhancement is used, we need AbstractInterpolantAutomaton";
				((AbstractInterpolantAutomaton<L>) subtrahend).switchToReadonlyMode();

			}

			if (!useErrorAutomaton) {
				// TODO alot of sanity checks dont think its required
				// checkEnhancement(subtrahendBeforeEnhancement, subtrahend);
			}

			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					// TODO merge removed hoare annotation stuff
				}
				diff.removeDeadEnds();
			}

		} finally {
			mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());
			mLogger.info(htc.getStatistics());
			mLogger.info(htc);
			mLogger.debug("WORKER: Finished constructing difference");
			// mCegarLoopBenchmark.addEdgeCheckerData(htc.getStatistics());
			// mCegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			// mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
	}

	private RunningTaskInfo executeDifferenceTimeoutActions(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) throws AutomataLibraryException {
		final RunningTaskInfo runningTaskInfo =
				getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement, automatonType);
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			// mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
			// mPredicateFactoryResultChecking, mCounterexample, true);
		}
		return runningTaskInfo;
	}

	private RunningTaskInfo getDifferenceTimeoutRunningTaskInfo(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) {
		final String taskDescription = "WORKER: constructing difference of abstraction (" + minuend.size()
				+ "states) and " + automatonType + " automaton (currently " + subtrahend.size() + " states, "
				+ subtrahendBeforeEnhancement.size() + " states before enhancement)";
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	protected final IHoareTripleChecker getHoareTripleChecker() {
		final IHoareTripleChecker refinementHtc = mRefinementResult.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}
		// Use all edges of the interpolant automaton that is already constructed as an
		// initial cache for the Hoare triple checker.
		final HoareTripleCheckerCache initialCache =
				TraceAbstractionUtils.extractHoareTriplesfromAutomaton(mRefinementResult.getInfeasibilityProof());
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
				mPref.getHoareTripleChecks(), mCsToolkit, mRefinementResult.getPredicateUnifier(), initialCache);
	}

	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			subtrahend = interpolantAutomaton;
		} else {
			final AbstractInterpolantAutomaton<L> ia = constructInterpolantAutomatonForOnDemandEnhancement(
					interpolantAutomaton, predicateUnifier, htc, enhanceMode);
			subtrahend = ia;
			// if (mStoreFloydHoareAutomata) {
			// mFloydHoareAutomata.add(new Pair<>(ia, predicateUnifier));
			// }
		}
		return subtrahend;
	}

	protected AbstractInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancement(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton<L> result;
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
			result = constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE:
			result = constructInterpolantAutomatonForOnDemandEnhancementEager(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
		return result;
	}

	private NondeterministicInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancementEager(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
		final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
		return new NondeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
	}

	private DeterministicInterpolantAutomaton<L>
			constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(
					final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
					final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
					final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
		final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
		return new DeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
	}
}