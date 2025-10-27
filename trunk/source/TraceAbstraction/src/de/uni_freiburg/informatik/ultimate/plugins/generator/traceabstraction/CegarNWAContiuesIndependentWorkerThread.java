package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
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

	private final IUltimateServiceProvider mServices;

	// SMT solver warning
	private final CfgSmtToolkit mCsToolkit;
	final PredicateFactory mPredicateFactory;
	PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;

	// globally
	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	// each worker needs one of their own:
	private final int mIteration;
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
	private final SimplificationTechnique mSimplificationTechnique;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	// Globals for Difference (Interpolant Automaton Enhancement)
	protected static final boolean REMOVE_DEAD_ENDS = true;
	private final ParallelNwaCegarLoop<L, A> mMainThread;

	INestedWordAutomaton<L, IPredicate> mAbstraction;
	private final HashMap<Integer, NestedRun<L, ?>> mCounterexamples = new HashMap<>();

	int mFoundFeasiblePaths = 0;

	/*
	 * A continues worker that addionaly searches its own counterexamples Still put the results in the result queue
	 */
	public CegarNWAContiuesIndependentWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final CegarLoopStatisticsGenerator statistcs,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IIcfg<? extends IcfgLocation> icfg, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<IRun<L, ?>> workerTaskQueue) throws InterruptedException {

		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mRefinementResult = null;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mCegarLoopBenchmark = statistcs;
		mServices = services;
		mCsToolkit = csToolkit;
		mIcfg = icfg;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;

		final Thread workerThread = new Thread(() -> {
			try {
				executeThread();
			} catch (final InterruptedException | AutomataOperationCanceledException e) {
				throw new AssertionError(e);
			}
		});
		workerThread.start();
	}

	public void executeThread() throws InterruptedException, AutomataOperationCanceledException {
		mAbstraction = mMainThread.getAbstraction();

		mCounterexamples.putAll(mMainThread.mActiveCounterexamples);
		int workerIterations = 0;
		try {
			mCounterexample = searchForErrorTrace();
		} catch (final AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		while (true) {

			mAbstraction = mMainThread.getAbstraction();
			mLogger.debug("SymbolicExecutionWorker: " + mFoundFeasiblePaths);
			workerIterations += 1;
			final List<L> trace = mCounterexample.getWord().asList();
			mCurrentErrorLoc = mCounterexample.getSymbol(mCounterexample.getLength() - 2).getTarget();
			final int traceHash = trace.hashCode();
			mLogger.info("Starting Thread: " + Thread.currentThread().getId() + "# for Trace Check: " + traceHash);
			Thread.currentThread().setName("Worker for " + traceHash);

			final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
			final Counterexample<L> counterexample = new Counterexample<>(mCounterexample.getWord(), locations);
			final ITARefinementStrategy<L> strategy = setUpStrategy(counterexample);
			final LBool isCexResult = isCounterexampleFeasible(strategy);
			mLogger.debug("SAT-Worker CheckSat Done: " + isCexResult);
			if (isCexResult.equals(LBool.SAT)) {
				mFoundFeasiblePaths += 1;
				constructRefinementAutomaton(AbstractCegarLoop.AutomatonType.ERROR);
				try {
					mThreadResult = refineAbstractionInternally();
				} catch (final AutomataLibraryException e) {
					// TODO Auto-generated catch block
					throw new AssertionError(e);
				}
				mBlockingQueueForResults.put(mThreadResult);
			}

			mCounterexample = searchForErrorTrace();
			if (isCexResult.equals(LBool.SAT)) {
				// needs to be done after searching, since we are faster then the difference in main
				mCounterexamples.remove(traceHash);
			}

			boolean flag = false;
			while (mCounterexample == null) {
				mLogger.debug("--------Sat Continues Worker Stats--------");
				mLogger.debug(workerIterations);
				mLogger.info(mFoundFeasiblePaths);
				mLogger.info("SAT-Worker Going to sleep!!!");
				// wake up, if abstraction was refined, maybe there are new cex beyond the loop bound to explore
				ParallelNwaCegarLoop.refinementLock.wait();
				mAbstraction = mMainThread.getAbstraction();
				mLogger.info("SAT-Worker wakes up and searches for new Cex.");
				mCounterexample = searchForErrorTrace();
				flag = true;
			}
			if (flag) {
				mLogger.info("SAT-Worker continues with new abstraction.");
			}

		}
	}

	/*
	 * Search for an error trace in the current mAbstraction. First we try BFS, then IsEmptyParallel and finally DFS
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace() throws AutomataOperationCanceledException {
		final Set<IPredicate> possibleEndPoints = null;
		final IsEmpty<L, IPredicate> search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.debug("SymbolicExecutionWorker: Found new Counterexample via IsEmptyParallel!");
			final NestedRun<L, IPredicate> counterexample = search.getNestedRun();
			final List<L> trace = counterexample.getWord().asList();
			final int traceHash = trace.hashCode();
			if (mCounterexamples.containsKey(traceHash)) {
				throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
			}
			mCounterexamples.put(traceHash, counterexample);
			return counterexample;
		}
		mLogger.debug("SymbolicExecutionWorker: Did not Find a Counterexample!");
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
	 * TODO what needs to be done once and what needs to be done for every CEX??????????ß
	 *
	 */
	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) throws InterruptedException {

		final PathProgramCache<L> cacheNotNeeded = new PathProgramCache<>(mLogger);
		final StrategyFactory<L> mStrategyFactory =
				new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs, mIcfg, mPredicateFactory,
						mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz, cacheNotNeeded);

		final ITARefinementStrategy<L> strategy;

		strategy = mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
				new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration),
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

	public void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType)
			throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			constructErrorAutomaton();
			break;
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
	 * construct only Error Automata
	 *
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

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(subtrahend, subtrahendBeforeEnhancement,
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCsToolkit.getManagedScript(), mCounterexample, mPredicateFactory,
				mRefinementResult.somePerfectSequenceFound(), true, false);
		return workerResult;
	}
}
