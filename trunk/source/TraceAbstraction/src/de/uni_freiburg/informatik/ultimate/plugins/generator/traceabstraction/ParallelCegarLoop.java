package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.TestGoalAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.WorkerPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.ParallelRefinementStrategy;

public class ParallelCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {

	boolean mComputeHoareAnnotation;
	private final IIcfg<?> mRootNode;
	final String mDestroyEverything = "destroyEverything";

	// Parallel Setup
	private final ExecutorService mExec;
	private int mThreadLimit;
	private int mRunningThreads = 0;

	// private final CompletionService<WorkerThreadResult<L, A>> mECS;
	BlockingQueue<Future<WorkerThreadResult<L, A>>> mWorkerResultQueue = new LinkedBlockingQueue<>();

	// Strategies
	private final HashMap<Integer, NestedRun<L, ?>> mAllCounterexamples = new HashMap<>();
	private final HashMap<HashSet<L>, ParallelRefinementStrategy<L>> mPpStrategyMap = new HashMap<>();

	// Testing Strategies
	private final boolean useGoalSetForIsEmpty;
	private final Set<IPredicate> mActiveErrorLocs = new HashSet<>();
	private final HashMap<Integer, Integer> mInActiveErrorLocs = new HashMap<>();

	// Addtional Statistiks for Evaluation
	private Integer mCounterexamplesChecked = 0;
	private Integer mRefinementsDone = 0;
	private final Integer mCountTimeoutsInSearch = 0;
	private final Integer mCountFailedRunConstructions = 0;
	private Integer mCountFailedToFindCex = 0;
	private Integer mCountBfsFoundCex = 1;
	private final Integer mCountIsEmptyParallel = 0;
	private Integer maxActiveThreads = 0;
	private final long mSearchTime = 0;
	private int mIterationsWithMaxThreads = 0;
	private int mIterationsWithOneThread = 0;
	private int mExceptionInWorker = 0;
	// need global program cache, but worker need to get copy otherwise we synchronize
	private final PathProgramCache<L> mProgramCache = new PathProgramCache<>(mLogger);

	/**
	 *
	 * Compute Initial Abstraction, can be reused
	 *
	 *
	 * Search a mCounterexample in Abstraction - Inital Abstraction returns true if counterexample -
	 * isAbstractionEmpty()
	 *
	 * TODO option to save memory, measure heap, then dont copy the abstracion on the worker
	 *
	 * @param name
	 * @param initialAbstraction
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param interpolation
	 * @param computeHoareAnnotation
	 * @param hoareAnnotationLocs
	 * @param services
	 * @param transitionClazz
	 * @param stateFactoryForRefinement
	 */

	public ParallelCegarLoop(final DebugIdentifier name, final INestedWordAutomaton<L, IPredicate> initialAbstraction,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<? extends IcfgLocation> errorLocs,
			final NwaHoareProofProducer<L> proofProducer, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);

		mRootNode = rootNode;

		// Start thread pool
		mThreadLimit = mPref.getThreadLimit();
		if (mThreadLimit == 0) { // maximum of available cores
			mThreadLimit = Runtime.getRuntime().availableProcessors();
			mThreadLimit -= 1; // one for main thread
		}
		mExec = Executors.newFixedThreadPool(mThreadLimit);
		// mECS = new ExecutorCompletionService<>(mExec);

		useGoalSetForIsEmpty = mPref.useGoalSetForIsEmpty;
		// mParallelSearchSrategy = mPref.parallelSearchSrategy;

		Thread.currentThread().setName("Main Cegar Thread");
		getServices().getStorage().pushMarker(mDestroyEverything);

	}

	/*
	 * sets up the worker with its own cfg script and its own RefinementStrategy
	 */
	private CegarWorkerThread<L, A> setUpWorker(final IUltimateServiceProvider iterationServices,
			final IcfgLocation currentErrorLoc, final int module) {
		// mCsToolkit needs to give new mgdScript for each thread

		final CfgSmtToolkit freshToolKit =
				mCsToolkit.getCfgSmtToolkitWithFreshScript(iterationServices, getSolverSettings(iterationServices,
						mIteration + mRunningThreads + mCounterexample.getWord().asList().hashCode() + "parallel"));
		// Set the Main Script
		((HistoryRecordingScript) freshToolKit.getManagedScript().getScript())
				.setMainScript(mCsToolkit.getManagedScript());

		// Fill the map from worker tv to main tv so we can obtain boogievars later
		final Map<TermVariable, IProgramVar> varMap =
				((Boogie2SmtSymbolTable) mCsToolkit.getSymbolTable()).getSmtVar2ProgramVarMap();

		for (final TermVariable tv : varMap.keySet()) {
			((HistoryRecordingScript) freshToolKit.getManagedScript().getScript()).addTermVariableToMap(
					(TermVariable) ((HistoryRecordingScript) freshToolKit.getManagedScript().getScript())
							.transferTermToWorker(tv),
					tv);
		}

		// Create predicateFactory with worker script
		final WorkerPredicateFactory predicateFactory =
				new WorkerPredicateFactory(mServices, freshToolKit.getManagedScript(), freshToolKit.getSymbolTable());

		// Create PredicateFactoryForInterpolantAutomata with worker script
		final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata =
				new PredicateFactoryForInterpolantAutomata(freshToolKit.getManagedScript(), predicateFactory,
						mComputeHoareAnnotation);

		final Set<IcfgLocation> hoareAnnotationLocs = Collections.emptySet();
		if (mComputeHoareAnnotation) {
			// TODO need different hoareAnnotationLocs
			throw new AssertionError("Hoare Annotations not yet supported in Parallel cegar loop");
		}
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				freshToolKit.getManagedScript(), predicateFactory, mComputeHoareAnnotation, hoareAnnotationLocs);

		// copy everything TODO: copy service, all globals at the end of this method
		// final TAPreferences tap = new TAPreferences(mServices);
		// final ILogger dummyLogger = ILogger.getDummyLogger();
		final PathProgramCache<L> cacheCopy = new PathProgramCache<>(mLogger);

		// make sure that mPref.getCfgSmtToolkit returns the worker toolkit
		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(getServices(), mPref, mInterpolationTechnique,
						mSimplificationTechnique, freshToolKit, predicateFactory, mIcfg);

		cacheCopy.copyCache(mProgramCache);
		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs,
				mIcfg, predicateFactory, predicateFactoryInterpolantAutomata, mTransitionClazz, cacheCopy);

		final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
		final var counterexample = new Counterexample<>(mCounterexample.getWord(), locations);

		// TODO deal with parallel

		final HashSet<L> pathProgramRepresentative = new HashSet<>(mCounterexample.getWord().asSet());

		final ParallelRefinementStrategy<L> parallelStrategy = mPpStrategyMap.get(pathProgramRepresentative);
		// TODO only increase cache if module == 0, need new constuct strategy
		final ITARefinementStrategy<L> strategy;
		if (module == -1) { // TODO better case distiction
			strategy = strategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
					predicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
					mPref.getRefinementStrategy(), mProgramCache);
		} else {

			// setup the strategy from getRefinementStrategy() such that the factory has the modules
			strategy = strategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
					predicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
					mPref.getRefinementStrategy(), mProgramCache, parallelStrategy, module);
		}
		// create a new strategy that has only one module, the one we want to use for this worker

		// start worker
		return new CegarWorkerThread<>(mLogger, mPref, mCounterexample, mAStarRandomHeuristicSeed, mResultBuilder,
				mCegarLoopBenchmark, iterationServices, freshToolKit, strategyFactory, predicateFactory,
				predicateFactoryInterpolantAutomata, stateFactoryForRefinement, mComputeHoareAnnotation, strategy,
				currentErrorLoc, mRootNode, this, parallelStrategy.generalize());
	}

	/*
	 * Parallel CEGAR loop of main thread In each iteration we pick a counterexample and setup a worker to check its
	 * feasibility
	 *
	 * The worker future contains either an interpolant or an error automaton.
	 *
	 * As soon as we obtain a worker result, we refine our abstraction. If abstraction is not empty, continue with the
	 * loop If no worker is done, continue with the loop If no thread is available and no worker is done we sleep
	 */
	@Override
	protected void iterate() throws AutomataLibraryException {
		// TODO manage time and timeout
		boolean didntFindCexLastIteration = false;

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			abortIfTimeout();
			boolean abstractionWasRefined = false;
			mLogger.info(String.format("=== Iteration %s ===", mIteration));

			try {
				try {
					// we sleep if not: thread or counterexample is available
					Future<WorkerThreadResult<L, A>> doneFuture = getWorkerResult(didntFindCexLastIteration);

					// go through all done Futures
					while (doneFuture != null) {
						try {
							final WorkerThreadResult<L, A> workerResult = doneFuture.get();
							mLogger.info("Main: A Thread is Done");

							// If Error automaton terminate immediately
							if (mPref.stopAfterFirstViolation()
									&& workerResult.getAutomatonType().equals(AutomatonType.ERROR)) {
								shutDownAndDestroy(mDestroyEverything);
								return;
							}

							// Only for test case generation
							updateTestGoalSet(workerResult);

							mLogger.info("Worker Automaton Type: " + workerResult.getAutomatonType());

							// Refine abstraction
							mLogger.info("Refining Abstraction");
							mRefinementsDone += 1;
							refinement(workerResult);
							abstractionWasRefined = true;

							// Not sure if necessary
							workerResult.garbageCollect();

							// If new abstraction is empty terminate immediately
							if (isSafeThenTerminate()) {
								return;
							}

						} catch (final ExecutionException | InterruptedException e) {
							e.printStackTrace();
							mLogger.warn("Trace Check Failed!!");
							mExceptionInWorker += 1;
							doneFuture.exceptionNow();
							// mExec.shutdownNow();
							// throw new AutomataLibraryException(null, e.getMessage());
						} catch (final CancellationException e) {
							mLogger.warn("Worker was cancelled!");
						} finally {

						}
						doneFuture = mWorkerResultQueue.poll();
					}

					assert doneFuture == null;

				} catch (AutomataOperationCanceledException | ToolchainCanceledException e) {
					// TODO deal with UNKNOWN
					throw e;
				} catch (final InterruptedException e1) {
					// TODO Auto-generated catch block, not used atm
					e1.printStackTrace();
				}

				if (abstractionWasRefined && !mPref.minimizeAbstractionPerWorker) {
					minimizeAbstractionIfEnabled(); // TODO warning uses NWA CEGAR loop
				}

				// need a new counterexample if the last one was used
				// or the abstraction was refined and we hope to find a better one
				// dont search for counterexamples unnecessarily BUSY WAITING!
				if ((mCounterexample == null && !didntFindCexLastIteration) || abstractionWasRefined) {
					mLogger.info("Searching for Counterexample");
					mCounterexample = searchForErrorTrace(false);
					if (mCounterexample == null) {
						didntFindCexLastIteration = true;
					}
				}

				// Doesnt Need to come before search because of initial counterexample, we skip search
				// mCounterexample can be null if no counterexample was found, but threads are still running
				while (mRunningThreads < mThreadLimit && mCounterexample != null) {
					startWorker();
					// mCounterexample is being checked, make sure next thread gets a new one
					mCounterexample = searchForErrorTrace(true);
				}

				updateAndPrintStatistics();
			} finally {

			}

		}
		mExec.shutdownNow();
		mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);

	}

	private void updateAndPrintStatistics() {
		if (mRunningThreads > maxActiveThreads) {
			maxActiveThreads = mRunningThreads;
		}
		if (mRunningThreads == mThreadLimit) {
			mIterationsWithMaxThreads += 1;
		}
		if (mRunningThreads == 1) {
			mIterationsWithOneThread += 1;
		}
		mLogger.info("Iteration " + getIteration());
		mLogger.info("Refinements: " + mRefinementsDone);
		mLogger.info("Counterexamples: " + mCounterexamplesChecked);
		mLogger.info("SearchTimeout: " + mCountTimeoutsInSearch);
		mLogger.info("RunConstructionFailed: " + mCountFailedRunConstructions);
		mLogger.info("SearchFailed: " + mCountFailedToFindCex);
		mLogger.info("BFS: " + mCountBfsFoundCex);
		mLogger.info("IsEmptyParallel: " + mCountIsEmptyParallel);
		mLogger.info("ActiveThreads: " + maxActiveThreads);
		mLogger.info("IterationsWithMaxThreads: " + mIterationsWithMaxThreads);
		mLogger.info("IterationsWithONEThread: " + mIterationsWithOneThread);
		mLogger.info("SearchTime: " + mSearchTime);
		mLogger.info("ExceptionInWorker: " + mExceptionInWorker);
	}

	private boolean isSafeThenTerminate() throws AutomataOperationCanceledException {
		// If IsEmpty says its empty, then we can terminate even if threads are still running
		if (super.isAbstractionEmpty() || mAbstraction.size() == 0) {
			mResultBuilder.addResultForAllRemaining(Result.SAFE);
			shutDownAndDestroy(mDestroyEverything);
			return true;
		}
		// set cex to null to be certain we don check counterexamples from the old abstraction
		mCounterexample = null;
		return false;
	}

	private void updateTestGoalSet(final WorkerThreadResult<L, A> workerResult) {
		// In useGoalSetForIsEmpty mode we omit error automata
		if (useGoalSetForIsEmpty) {
			final List<L> trace = workerResult.getCounterexample().getWord().asList();
			final int traceHash = trace.hashCode();
			final Integer testGoalId = mInActiveErrorLocs.get(traceHash);
			mLogger.info("Done TestGoal: " + testGoalId);
			if (workerResult.getAutomatonType().equals(AutomatonType.FLOYD_HOARE)) {
				mInActiveErrorLocs.remove(traceHash);
			}
		}
	}

	private void startWorker() {
		mLogger.info("Main: Starting Thread");
		final IcfgLocation currentErrorLoc = getErrorLocFromCounterexample();
		final IUltimateServiceProvider iterationServices = createIterationTimer(currentErrorLoc);
		mServices = iterationServices;
		final RefinementStrategy strategyType;
		final ExecutorService executor;
		final HashSet<L> ppRepresentative = new HashSet<>(mCounterexample.getWord().asSet());

		if (!mPpStrategyMap.containsKey(ppRepresentative)) {
			mPpStrategyMap.put(ppRepresentative,
					new ParallelRefinementStrategy<>(mLogger, ppRepresentative, mThreadLimit));
			updateExecutorSizes();
			mRunningThreads += 1;
		}
		final ParallelRefinementStrategy<L> pathProgramStrategy = mPpStrategyMap.get(ppRepresentative);
		executor = pathProgramStrategy.getExecutor();

		assert (!executor.isTerminated());// {

		// setting how many thread we want to start per counterexample.
		// Plan 2 threads one is always craig on interpol as quickecheckr

		for (int module = 0; module < 2; module++) {
			if (pathProgramStrategy.isActiveModule(module)) {
				// strategies
				final CegarWorkerThread<L, A> worker =
						setUpWorker(iterationServices, currentErrorLoc, pathProgramStrategy.getRunningThreadsOfPP());
				mWorkerResultQueue.add(executor.submit(worker));

			}
		}
		// } else {
		// final CegarWorkerThread<L, A> worker = setUpWorker(iterationServices, currentErrorLoc, -1);
		// mWorkerResultQueue.add(mExec.submit(worker));
		// mRunningThreads += 1;
		// }
		// strategies
		// final CegarWorkerThread<L, A> worker = setUpWorker(iterationServices, currentErrorLoc);
		// worker is a Callable and is called here
		// mExec.submit(worker);
		// mWorkerResultQueue.add(executor.submit(worker));
		// mRunningThreads += 1;
		mCounterexamplesChecked += 1;
		// add mCounterexample to list such that we dont get it twice in our search
		addCounterexampleToSet((NestedRun<L, ?>) mCounterexample);
	}

	private Future<WorkerThreadResult<L, A>> getWorkerResult(final boolean didntFindCexLastIteration)
			throws InterruptedException {
		Future<WorkerThreadResult<L, A>> doneFuture = null;
		if (mRunningThreads == mThreadLimit || didntFindCexLastIteration) {
			assert mRunningThreads > 0;
			mLogger.info("All threads busy, going to sleep.");
			// No busy waiting via BlockingQueue
			doneFuture = mWorkerResultQueue.take(); // TODO exception handling
			mLogger.info("Waking up, a worker is done.");
		} else {
			doneFuture = mWorkerResultQueue.poll();
		}

		return doneFuture;
	}

	private void shutDownAndDestroy(final Object marker) {
		mExec.shutdownNow();
		final Set<String> destroyedStorables = getServices().getStorage().destroyMarker(marker);
		if (!destroyedStorables.isEmpty()) {
			mLogger.warn("Destroyed unattended storables created during the last iteration: "
					+ destroyedStorables.stream().collect(Collectors.joining(",")));
		}
	}

	private void refinement(final WorkerThreadResult<L, A> threadResult)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		assert threadResult.getAutomatonType().equals(AutomatonType.FLOYD_HOARE);

		// mInterations equals the amount of refinements
		mCegarLoopBenchmark.announceNextIteration();

		final List<L> trace = threadResult.getCounterexample().getWord().asList();
		final int traceHash = trace.hashCode();
		mLogger.info("Subtrahend traceHash: " + traceHash);

		// Only remove after the counterexample is no longer in the abstraction
		if (mPref.considerOnlyActiveCounterexamplesInIsEmptyParallel) {
			mAllCounterexamples.remove(traceHash);
		}

		final Set<IcfgLocation> hoareAnnotationLocs;
		// if (mComputeHoareAnnotation) {
		// hoareAnnotationLocs = (Set<IcfgLocation>) TraceAbstractionUtils
		// .getLocationsForWhichHoareAnnotationIsComputed(mRootNode, mPref.getHoareAnnotationPositions());
		// } else {
		hoareAnnotationLocs = Collections.emptySet();
		// }

		final PredicateFactoryRefinement stateFactoryForRefinement =
				new PredicateFactoryRefinement(getServices(), threadResult.getWorkerMgdScript(),
						threadResult.getPredicateFactory(), mComputeHoareAnnotation, hoareAnnotationLocs);
		mLogger.info("Difference in Main");
		final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff =
				computeAutomataDifference(mAbstraction, threadResult, stateFactoryForRefinement);

		mAbstraction = diff.getResult();

		if (mPref.minimizeAbstractionPerWorker) {
			minimizeAbstractionIfEnabled(stateFactoryForRefinement,
					new PredicateFactoryResultChecking(mPredicateFactory));
		}

		// If perfect terminate ThreadGroup (executor) else free the module
		final HashSet<L> pathProgramRepresentative = new HashSet<>(threadResult.getCounterexample().getWord().asSet());
		// TODO it can be that we have multiple perfect sequences and the pp is already removed from the map
		if (threadResult.wasPerfect() && mPpStrategyMap.containsKey(pathProgramRepresentative)) {
			assert mPpStrategyMap.containsKey(pathProgramRepresentative);
			mPpStrategyMap.get(pathProgramRepresentative).getExecutor().shutdown();
			mPpStrategyMap.remove(pathProgramRepresentative);
			updateExecutorSizes();
			mRunningThreads -= 1;
		} else if (mPpStrategyMap.containsKey(pathProgramRepresentative)) {
			mPpStrategyMap.get(pathProgramRepresentative).reportImperfectSequence(getServices(),
					stateFactoryForRefinement, mAbstraction);
		}

		// Kill the worker script
		((HistoryRecordingScript) threadResult.getWorkerMgdScript().getScript()).exit();

		// Removed 26.1.25: iterate over active counterexamples, check if included else kill worker
		mLogger.info("Refinement done.");
	}

	/*
	 * We update the threadlimits of all executors that we have. The new Value is the mThreadLimit divided by the
	 * current path programs. Ideally every executor has already multiple threads sheduled
	 */
	private void updateExecutorSizes() {
		if (mPpStrategyMap.isEmpty()) {
			return;
		}
		int newSize = mThreadLimit / mPpStrategyMap.size();
		if (newSize == 0) {
			newSize += 1;
		}
		for (final ParallelRefinementStrategy<L> strategy : mPpStrategyMap.values()) {
			strategy.updateExecutorSizes(newSize);
		}
	}

	private void updateActiveTestGoals() {
		assert useGoalSetForIsEmpty;
		final List<?> sequence = mCounterexample.getStateSequence();
		final IPredicate currentGoal = (IPredicate) sequence.get(sequence.size() - 1);
		assert mActiveErrorLocs.contains(currentGoal);
		// mark test goal as busy/occupied
		final ISLPredicate testGoalISL = (ISLPredicate) currentGoal;
		final IAnnotations pLocAnno =
				testGoalISL.getProgramPoint().getPayload().getAnnotations().get(TestGoalAnnotation.class.getName());
		final List<L> trace = mCounterexample.getWord().asList();
		final int traceHash = trace.hashCode();
		// use traceHash as identifier so we can calculate the identifier later
		mInActiveErrorLocs.put(traceHash, ((TestGoalAnnotation) pLocAnno).mId);
		// WARNING all goals can be in mInActiveErrorLocs, but we are not done yet!!
	}

	/*
	 * Only add a counterexample if it is being checked by a thread otherwise we are unsound
	 */
	private void addCounterexampleToSet(final NestedRun<L, ?> counterexample) {
		final List<L> trace = counterexample.getWord().asList();
		final int traceHash = trace.hashCode();
		if (mAllCounterexamples.containsKey(traceHash)) {
			throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
		}
		mAllCounterexamples.put(traceHash, counterexample);
	}

	/*
	 * Potential Data Race?, Main thread can refine abstraction while worker uses it. Doesnt seem to be a problem so far
	 *
	 * Alternative: Give a real copy to the worker, leads to more mem consumption
	 */
	public INestedWordAutomaton<L, IPredicate> getAbstraction() {
		return mAbstraction;
	}

	private IsEmpty<L, IPredicate> getSearch(final IsEmpty.SearchStrategy strategy,
			final Set<IPredicate> possibleEndPoints) throws AutomataOperationCanceledException {
		switch (strategy) {
		case PARALLEL:
			return new IsEmptyParallel<>(new AutomataLibraryServices(mServices), mAbstraction,
					mAbstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints, true,
					IsEmpty.SearchStrategy.BFS, mAllCounterexamples);
		default:
			return new IsEmpty<>(new AutomataLibraryServices(mServices), mAbstraction, mAbstraction.getInitialStates(),
					Collections.emptySet(), Collections.emptySet(), strategy);
		}
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
			if (mAllCounterexamples.containsKey(traceHash)) {
				fresh = false;
			}
			return correct && fresh;
		}
		return false;
	}

	/*
	 * Search for an error trace in the current mAbstraction. First we try BFS, then IsEmptyParallel and finally DFS
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace(final boolean onlyDoIsEmptyParallel)
			throws AutomataOperationCanceledException {
		Set<IPredicate> possibleEndPoints = null;
		/*
		 * Optimization that ensures we find a trace to a not yet targeted test goal / error loc
		 */
		if (useGoalSetForIsEmpty) {
			mActiveErrorLocs.clear();
			for (final IPredicate testGoal : mAbstraction.getFinalStates()) {
				final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
				final IAnnotations pLocAnno = testGoalISL.getProgramPoint().getPayload().getAnnotations()
						.get(TestGoalAnnotation.class.getName());
				if (mInActiveErrorLocs.containsValue(((TestGoalAnnotation) pLocAnno).mId)) {
					continue;
				}
				if (pLocAnno instanceof TestGoalAnnotation) {
					mActiveErrorLocs.add(testGoal);
				}
			}
			if (mActiveErrorLocs.isEmpty()) {
				return null;
			}
			possibleEndPoints = mActiveErrorLocs;

			updateActiveTestGoals();
		}
		if (onlyDoIsEmptyParallel) {
			final IsEmpty<L, IPredicate> search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
			if (isSearchCorrectAndTraceFresh(search)) {
				mLogger.info("Found new Counterexample via IsEmptyParallel!");
				return search.getNestedRun();
			}
			mLogger.info("Did not Find a Counterexample!");
			mCountFailedToFindCex += 1;
			assert mRunningThreads > 0;
			return null;
		}

		IsEmpty<L, IPredicate> search = getSearch(IsEmpty.SearchStrategy.BFS, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mCountBfsFoundCex += 1;
			mLogger.info("Found new Counterexample via BFS!");
			return search.getNestedRun();
		}
		search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.info("Found new Counterexample via IsEmptyParallel!");
			return search.getNestedRun();
		}
		search = getSearch(IsEmpty.SearchStrategy.DFS, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.info("Found new Counterexample via DFS!");
			return search.getNestedRun();
		}

		mLogger.info("Did not Find a Counterexample!");
		mCountFailedToFindCex += 1;
		assert mRunningThreads > 0;
		return null;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		// Worker does the enhancement or nobody!
		subtrahend = interpolantAutomaton;
		return subtrahend;
	}

	/*
	 * Difference is calculated twice first in worker and then in master. We need the worker CFG script here
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend, final WorkerThreadResult<L, A> workerResult,
			final PredicateFactoryRefinement stateFactoryForRefinement)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");

			final PowersetDeterminizer<L, IPredicate> psd = new PowersetDeterminizer<>(workerResult.getSubtrahend(),
					true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, workerResult.exploitSigmaStarConcatOfIa());
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(workerResult.getSubtrahend().size());

			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				throw tce;
			} finally {
				// We never enhance in main thread!
			}

			if (!workerResult.useErrorAutomaton()) {
				// TODO needs to get the worker counterexample
				// checkEnhancement(workerResult.getSubtrahendBeforeEnhancement(), workerResult.getSubtrahend());
			}
			// Future work:
			assert !mPref.dumpOnlyReuseAutomata();
			assert mFaultLocalizationMode == RelevanceAnalysisMode.NONE;

			if (REMOVE_DEAD_ENDS) {
				diff.removeDeadEnds();
			}
			return diff;
		} finally {
		}
	}

	/**
	 * @param services
	 * @param filename
	 */
	private SolverSettings getSolverSettings(final IUltimateServiceProvider services, final String filename) {

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		final SolverMode solverMode = prefs.getEnum(RcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);

		final boolean fakeNonIncrementalScript =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final boolean compressSmtScript = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
		final String pathOfDumpedScript = prefs.getString(RcfgPreferenceInitializer.LABEL_DUMP_PATH);

		final String commandExternalSolver = prefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);

		final boolean dumpUnsatCoreTrackBenchmark =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions =
				prefs.getKeyValueMap(RcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);

		final Logics logicForExternalSolver =
				Logics.valueOf(prefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename, compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);

		return solverSettings;
	}

	private void minimizeAbstractionIfEnabled(final PredicateFactoryRefinement stateFactoryForRefinement,
			final PredicateFactoryResultChecking predicateFactoryResultChecking)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {
		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
			// do not apply minimization
			break;
		case DFA_HOPCROFT_LISTS:
		case DFA_HOPCROFT_ARRAYS:
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
		case NWA_MAX_SAT:
		case NWA_MAX_SAT2:
		case RAQ_DIRECT_SIMULATION:
		case RAQ_DIRECT_SIMULATION_B:
		case NWA_COMBINATOR_PATTERN:
		case NWA_COMBINATOR_EVERY_KTH:
		case NWA_OVERAPPROXIMATION:
		case NWA_COMBINATOR_MULTI_DEFAULT:
		case NWA_COMBINATOR_MULTI_SIMULATION:
			// apply minimization
			minimizeAbstraction(stateFactoryForRefinement, predicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
	}

	/**
	 * Automata theoretic minimization of the automaton stored in mAbstraction. Expects that mAbstraction does not have
	 * dead ends.
	 *
	 * @param predicateFactoryRefinement
	 *            PredicateFactory for the construction of the new (minimized) abstraction.
	 * @param resultCheckPredFac
	 *            PredicateFactory used for auxiliary automata used for checking correctness of the result (if
	 *            assertions are enabled).
	 */
	@Override
	protected void minimizeAbstraction(final PredicateFactoryRefinement predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {

		final Function<IPredicate, Set<IcfgLocation>> lcsProvider =
				x -> (x instanceof ISLPredicate ? Collections.singleton(((ISLPredicate) x).getProgramPoint())
						: new HashSet<>(Arrays.asList(((IMLPredicate) x).getProgramPoints())));
		AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
		try {
			am = new AutomataMinimization<>(getServices(), mAbstraction, minimization, mComputeHoareAnnotation,
					getIteration(), predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION,
					mStoredRawInterpolantAutomata, mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac,
					lcsProvider, true);
		} catch (final AutomataMinimizationTimeout e) {
			mCegarLoopBenchmark.addAutomataMinimizationData(e.getStatistics());
			throw e.getAutomataOperationCanceledException();
		}
		mCegarLoopBenchmark.addAutomataMinimizationData(am.getStatistics());
		final boolean newAutomatonWasBuilt = am.newAutomatonWasBuilt();

		if (newAutomatonWasBuilt) {
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<L, IPredicate> newAbstraction = am.getMinimizedAutomaton();

			// extract Hoare annotation
			if (mComputeHoareAnnotation) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
				}
				// mHaf.updateOnMinimization(oldState2newState, newAbstraction);
			}

			// statistics
			final int oldSize = mAbstraction.size();
			final int newSize = newAbstraction.size();
			assert oldSize == 0 || oldSize >= newSize : "Minimization increased state space";

			// use result
			mAbstraction = newAbstraction;
		}
	}
}

final class WorkerThreadResult<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mSubtrahend;
	private AutomatonType mAutomatonType;
	private final boolean mUseErrorAutomaton;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mSubtrahendBeforeEnhancement;
	private InterpolantAutomatonEnhancement mEnhanceMode;
	private final boolean mExploitSigmaStarConcatOfIa;
	private ManagedScript mMgdScript;
	private IRun<L, ?> mCounterexample;
	PredicateFactory mPredicateFactory;
	private final boolean mWasPerfect;

	/**
	 * @param automatonType
	 * @param predicateFactory
	 *
	 *
	 */
	WorkerThreadResult(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final InterpolantAutomatonEnhancement enhanceMode, final boolean useErrorAutomaton,
			final AutomatonType automatonType, final ManagedScript mgdScript, final IRun<L, ?> counterexample,
			final PredicateFactory predicateFactory, final boolean wasPerfect) {
		mSubtrahend = subtrahend;
		mAutomatonType = automatonType;
		mUseErrorAutomaton = useErrorAutomaton;
		mEnhanceMode = enhanceMode;
		mSubtrahendBeforeEnhancement = subtrahendBeforeEnhancement;
		mExploitSigmaStarConcatOfIa = explointSigmaStarConcatOfIA;
		mMgdScript = mgdScript;
		mCounterexample = counterexample;
		mPredicateFactory = predicateFactory;
		mWasPerfect = wasPerfect;
	}

	public IIpTcStrategyModule<?, L> getModule() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean wasPerfect() {
		return mWasPerfect;
	}

	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	public InterpolantAutomatonEnhancement getEnhanceMode() {
		return mEnhanceMode;
	}

	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getSubtrahend() {
		return mSubtrahend;
	}

	public AutomatonType getAutomatonType() {
		return mAutomatonType;
	}

	public boolean useErrorAutomaton() {
		return mUseErrorAutomaton;
	}

	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getSubtrahendBeforeEnhancement() {
		return mSubtrahendBeforeEnhancement;
	}

	public boolean exploitSigmaStarConcatOfIa() {
		return mExploitSigmaStarConcatOfIa;
	}

	public ManagedScript getWorkerMgdScript() {
		return mMgdScript;
	}

	public IRun<L, ?> getCounterexample() {
		return mCounterexample;
	}

	public void garbageCollect() {
		mSubtrahend = null;
		mAutomatonType = null;
		mEnhanceMode = null;
		mSubtrahendBeforeEnhancement = null;
		mMgdScript = null;
		mCounterexample = null;
	}
}
