package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.TestGoalAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class CegarNWAContiuesIndependentWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

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
	private int mIteration = 1;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;

	// each worker needs one of their own, but creates it themself:
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult;

	TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;

	// ???
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	boolean mComputeHoareAnnotation;

	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	protected IRun<L, ?> mCounterexample = null;

	private IcfgLocation mCurrentErrorLoc;

	// for error automata
	private final boolean mUseGoalSetForIsEmpty;
	private final SimplificationTechnique mSimplificationTechnique;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	// Globals for Difference (Interpolant Automaton Enhancement)
	protected static final boolean REMOVE_DEAD_ENDS = true;
	private final ParallelNwaCegarLoop<L, A> mMainThread;

	INestedWordAutomaton<L, IPredicate> mAbstraction;
	private final HashMap<Integer, NestedRun<L, ?>> mCounterexamples = new HashMap<>();

	private final ArrayList<Integer> mTestGoalTodoStack = new ArrayList<>();
	private final Set<Integer> mTestGoalWorkingSet = new HashSet<>();
	private final Set<Integer> mCoveredTestGoals = new HashSet<>();

	int mFoundFeasiblePaths = 0;

	/*
	 * A continues worker that addionaly searches its own counterexamples Still put the results in the result queue
	 */
	public CegarNWAContiuesIndependentWorkerThread(final ILogger logger, final TAPreferences pref,
			final CegarLoopResultBuilder resultBuilder, final CegarLoopStatisticsGenerator statistcs,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IIcfg<? extends IcfgLocation> icfg, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils) throws InterruptedException {

		mLogger = logger;
		mPref = pref;
		mRefinementResult = null;
		mResultBuilder = resultBuilder;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mCegarLoopBenchmark = statistcs;
		mServices = services;
		mCsToolkit = csToolkit;
		mIcfg = icfg;
		// mStrategyFactory = strategyFactory;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mUseGoalSetForIsEmpty = pref.useGoalSetForIsEmpty;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mNwaCexTransferrer = transferWorkerUtils;
		csToolkit.setQuickCheck();

	}

	@Override
	public void run() {
		try {
			mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
			Thread.sleep(120000);
			int maxId = -1;

			for (final IPredicate testGoal : mAbstraction.getFinalStates()) {
				final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
				final IAnnotations pLocAnno = testGoalISL.getProgramPoint().getPayload().getAnnotations()
						.get(TestGoalAnnotation.class.getName());

				if (pLocAnno instanceof TestGoalAnnotation) {
					mTestGoalTodoStack.add(((TestGoalAnnotation) pLocAnno).mId);
					if (((TestGoalAnnotation) pLocAnno).mId > maxId) {
						maxId = ((TestGoalAnnotation) pLocAnno).mId;
					}
				}
			}
			mTestGoalTodoStack.sort(null);
			if (maxId != -1) { // if not, not in test case generation mode
				mTestGoalWorkingSet.add(maxId);
			}
			// mTestGoalWorkingSet.addAll(mTestGoalTodoStack);

			int workerIterations = 0;
			try {
				mCounterexample = searchForErrorTrace();
			} catch (final AutomataOperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			while (true) {

				mLogger.debug("--------Sat Continues Worker Stats--------");
				mLogger.debug(workerIterations);
				mLogger.debug(mFoundFeasiblePaths);
				mLogger.debug(mCoveredTestGoals.size());

				workerIterations += 1;
				final List<L> trace = mCounterexample.getWord().asList();
				mCurrentErrorLoc = mCounterexample.getSymbol(mCounterexample.getLength() - 2).getTarget();
				final int traceHash = trace.hashCode();
				mLogger.debug("Starting Thread: " + Thread.currentThread().getId() + "# for Trace Check: " + traceHash);
				Thread.currentThread().setName("Worker for " + traceHash);

				final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
				final Counterexample<L> counterexample = new Counterexample<>(mCounterexample.getWord(), locations);
				final ITARefinementStrategy<L> strategy = setUpStrategy(counterexample);
				mLogger.debug("SAT-Worker CheckSat");
				final LBool isCexResult = isCounterexampleFeasible(strategy);
				mLogger.debug("SAT-Worker CheckSat Done: " + isCexResult);
				mLogger.debug("------------------------------------------");
				if (isCexResult.equals(LBool.SAT)) {

					mFoundFeasiblePaths += 1;
					final AbstractCegarLoop.AutomatonType automatonType =
							processFeasibilityCheckResult(isCexResult, mCurrentErrorLoc);

					constructRefinementAutomaton(automatonType);

					try {
						mThreadResult = refineAbstractionInternally();
					} catch (final AutomataLibraryException e) {
						// TODO Auto-generated catch block
						throw new AssertionError(e);
					}
					if (workerIterations % 10 == 0) {
						Thread.sleep(1000);
					}
					mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
					for (final Object testGoal : mThreadResult.getCounterexample().getStateSequence()) {
						final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
						final IAnnotations pLocAnno = testGoalISL.getProgramPoint().getPayload().getAnnotations()
								.get(TestGoalAnnotation.class.getName());
						if ((pLocAnno instanceof TestGoalAnnotation)) {
							// assert mTestGoalWorkingSet.contains(((TestGoalAnnotation) pLocAnno).mId);
							mCoveredTestGoals.add(((TestGoalAnnotation) pLocAnno).mId);
						}
					}

					mBlockingQueueForResults.put(mThreadResult);
				}

				mCounterexample = searchForErrorTrace();
				if (isCexResult.equals(LBool.SAT)) {
					// needs to be done after searching, since we are faster then the difference in main
					mCounterexamples.remove(traceHash);
				}

				if (!mTestGoalTodoStack.isEmpty() && workerIterations % 10 == 0) {
					mTestGoalWorkingSet.add(mTestGoalTodoStack.getLast());
					mTestGoalTodoStack.removeLast();
				}

				if (!mTestGoalTodoStack.isEmpty() && mTestGoalWorkingSet.isEmpty() && mCounterexample == null) {
					mTestGoalWorkingSet.add(mTestGoalTodoStack.getLast());
					mTestGoalTodoStack.removeLast();
				} else {
					boolean flag = false;
					while (mCounterexample == null) {
						mLogger.debug("--------Sat Continues Worker Stats--------");
						mLogger.debug(workerIterations);
						mLogger.debug(mFoundFeasiblePaths);
						mLogger.debug(mCoveredTestGoals.size());
						mLogger.debug("SAT-Worker Going to sleep!!!");
						synchronized (ParallelNwaCegarLoop.refinementLock) {
							ParallelNwaCegarLoop.refinementLock.wait();
							mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
						}
						mLogger.debug("SAT-Worker Waking Up !!!");
						// mCsToolkit.getManagedScript().getScript().exit();
						// break;
						mCounterexample = searchForErrorTrace();
						flag = true;
					}
					if (flag) {
						mLogger.debug("SAT-Worker Continues after waking up!!!");
					}

				}
				mIteration += 1;
			}
		} catch (final AutomataLibraryException | InterruptedException e) {

		}
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, Mode.MAIN2WORKER);
		return workerAbstraction;
	}

	/*
	 * Search for an error trace in the current mAbstraction. First we try BFS, then IsEmptyParallel and finally DFS
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace() throws AutomataOperationCanceledException {
		final Set<IPredicate> possibleEndPoints = null;// calculateGoals();

		final IsEmpty<L, IPredicate> search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.debug("Found new Counterexample via IsEmptyParallel!");
			final NestedRun<L, IPredicate> counterexample = search.getNestedRun();
			final List<L> trace = counterexample.getWord().asList();
			final int traceHash = trace.hashCode();
			if (mCounterexamples.containsKey(traceHash)) {
				throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
			}
			mCounterexamples.put(traceHash, counterexample);
			return counterexample;
		}
		mLogger.debug("Did not Find a Counterexample!");
		return null;
	}

	private Set<IPredicate> calculateGoals() {
		final Set<IPredicate> longTraceGoalStates = new HashSet<>();

		for (final IPredicate testGoal : mAbstraction.getFinalStates()) {
			final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
			final IAnnotations pLocAnno =
					testGoalISL.getProgramPoint().getPayload().getAnnotations().get(TestGoalAnnotation.class.getName());
			if ((pLocAnno instanceof TestGoalAnnotation)
					&& !mCoveredTestGoals.contains(((TestGoalAnnotation) pLocAnno).mId)
					&& mTestGoalWorkingSet.contains(((TestGoalAnnotation) pLocAnno).mId)) {
				longTraceGoalStates.add(testGoal);
			}
		}
		if (!longTraceGoalStates.isEmpty()) {
			return longTraceGoalStates;
		}
		return null;
	}

	private IsEmpty<L, IPredicate> getSearch(final IsEmpty.SearchStrategy strategy,
			final Set<IPredicate> possibleEndPoints) throws AutomataOperationCanceledException {
		return new IsEmptyParallel<>(new AutomataLibraryServices(mServices), mAbstraction,
				mAbstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints, possibleEndPoints == null,
				IsEmpty.SearchStrategy.BFS, mCounterexamples, mPref.mQuickCheckLoopBound);

	}

	private boolean isSearchCorrectAndTraceFresh(final IsEmpty<L, IPredicate> search) {
		boolean correct = false;
		boolean fresh = true;
		try {
			correct = search.checkResult(mStateFactoryForRefinement);
		} catch (final AutomataLibraryException e) {
			e.printStackTrace();
			assert false;
		}

		final NestedRun<L, IPredicate> run = search.getNestedRun();
		if (run != null) {
			final List<L> trace = run.getWord().asList();
			final int traceHash = trace.hashCode();
			if (mCounterexamples.containsKey(traceHash)) {
				fresh = false;
			}
			return correct && fresh;
		}
		return false;
	}

	protected List<?> getControlConfigurationsFromCounterexample(final IRun<L, ?> run) {
		if (IcfgUtils.isConcurrent(mIcfg)) {
			return run.getStateSequence().stream().map(p -> ((IMLPredicate) p).getProgramPoints())
					.collect(Collectors.toList());
		}
		return getIcfgLocationsFromRun(run);
	}

	private List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	/*
	 * sets up the worker with its own cfg script and its own RefinementStrategy
	 *
	 *
	 * TODO what needs to be done once and what needs to be done for every CEX??????????ß
	 *
	 * new constuct Strategy for every cex!
	 *
	 */

	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) throws InterruptedException {
		final StrategyFactory<L> mStrategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mIcfg, mPredicateFactory, mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz);
		final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), counterexample,
				mAbstraction, new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, 1),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				mPref.getRefinementStrategy());
		return strategy;
	}

	private IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	private IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	protected LBool isCounterexampleFeasible(final ITARefinementStrategy<L> strategy) {
		final TraceAbstractionRefinementEngine<L> refinementEngine =
				new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy, true);
		mRefinementResult = refinementEngine.getResult();
		return mRefinementResult.getCounterexampleFeasibility();
	}

	/**
	 * Report results from a feasibility check if necessary and return the type of the refinement automaton
	 *
	 * @param strategy
	 */
	public AbstractCegarLoop.AutomatonType processFeasibilityCheckResult(final LBool isCounterexampleFeasible,
			final IcfgLocation currentErrorLoc) {
		if (isCounterexampleFeasible == Script.LBool.SAT) {

			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			}
			return AbstractCegarLoop.AutomatonType.ERROR;
		}
		if (isCounterexampleFeasible != Script.LBool.UNKNOWN) {
			return AbstractCegarLoop.AutomatonType.INTERPOLANT;
		}
		Result actualResult;

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
			mLogger.debug("Excluding counterexample to continue analysis with %s automaton", automatonType);
			constructErrorAutomaton();
			break;
		case UNKNOWN:
			return;
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
				mRefinementResult.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction,
				mIteration);
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

		final BasicCegarLoop.AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;

		mErrorGeneralizationEngine.startDifference();
		automatonType = BasicCegarLoop.AutomatonType.ERROR;
		useErrorAutomaton = true;
		exploitSigmaStarConcatOfIa = false;
		enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
		subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
		subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(
				mNwaCexTransferrer.transferAutomaton(subtrahend, mStateFactoryForRefinement, Mode.WORKER2MAIN),
				mNwaCexTransferrer.transferAutomaton(subtrahendBeforeEnhancement, mStateFactoryForRefinement,
						Mode.WORKER2MAIN),
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCsToolkit.getManagedScript(),
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mCounterexample, Mode.WORKER2MAIN), mPredicateFactory,
				mRefinementResult.somePerfectSequenceFound(), true, false);
		return workerResult;
	}
}
