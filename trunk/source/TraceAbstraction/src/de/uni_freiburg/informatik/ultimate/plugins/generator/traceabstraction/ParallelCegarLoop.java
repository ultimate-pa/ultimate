package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.WorkerPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.TestGenerationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

public class ParallelCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {

	private final ArrayDeque<WorkerThreadResult<L, A>> automataWaitingList = new ArrayDeque<WorkerThreadResult<L, A>>();

	boolean mNoThreadFree;
	boolean mComputeHoareAnnotation;

	ExecutorService mExec;

	int mThreadLimit; // Runtime.avalablecores or so
	CompletionService<WorkerThreadResult<L, A>> mECS;
	private final IIcfg<?> mRootNode;

	private final Set<IPredicate> mActiveErrorLocs = new HashSet<>();
	private final HashMap<Integer, Integer> mInActiveErrorLocs = new HashMap<>(); // maps counterexample hash to test
																					// goal id
	final ArrayList<NestedRun<L, IPredicate>> mActiveCounterexamples = new ArrayList<>();

	// for debugging only, ensures our search does not find the same counterexampl twice
	private final HashMap<Integer, NestedRun<L, IPredicate>> mAllCounterexamples = new HashMap<>();

	private final boolean useGoalSetForIsEmpty;
	private final boolean mParallelSearchSrategy;

	// shared read only inital abstraction for automata generalization in threads
	private final INestedWordAutomaton<L, IPredicate> mInitialAbstraction;

	/**
	 *
	 * Compute Initial Abstraction, can be reused
	 *
	 *
	 * Search a mCounterexample in Abstraction - Inital Abstraction returns true if counterexample -
	 * isAbstractionEmpty()
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
			final InterpolationTechnique interpolation, final boolean computeHoareAnnotation,
			final Set<IcfgLocation> hoareAnnotationLocs, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation,
				computeHoareAnnotation, hoareAnnotationLocs, services, transitionClazz, stateFactoryForRefinement);

		mRootNode = rootNode;

		// Start thread pool
		mThreadLimit = mPref.getThreadLimit();
		if (mThreadLimit == 0) { // maximum of available cores
			mThreadLimit = Runtime.getRuntime().availableProcessors();
			mThreadLimit -= 1; // one for main thread
		}
		mExec = Executors.newFixedThreadPool(mThreadLimit);
		mECS = new ExecutorCompletionService<>(mExec);

		useGoalSetForIsEmpty = mPref.useGoalSetForIsEmpty;
		mParallelSearchSrategy = mPref.parallelSearchSrategy;
		mInitialAbstraction = initialAbstraction;
	}

	/*
	 * sets up the worker with its own cfg script and its own RefinementStrategy
	 */
	private CegarWorkerThread<L, A> setUpWorker(final IUltimateServiceProvider iterationServices,
			final int runningThreads, final IcfgLocation currentErrorLoc, final RefinementStrategy strategyType) {
		// mCsToolkit needs to give new mgdScript for each thread
		final CfgSmtToolkit freshToolKit =
				mCsToolkit.getCfgSmtToolkitWithFreshScript(iterationServices, getSolverSettings(iterationServices,
						mIteration + runningThreads + mCounterexample.hashCode() + "parallel"));
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
				new PredicateFactoryForInterpolantAutomata(freshToolKit.getManagedScript(), mPredicateFactory,
						mComputeHoareAnnotation);

		final Set<IcfgLocation> hoareAnnotationLocs = Collections.emptySet();
		if (mComputeHoareAnnotation) {
			assert false; // TODO needs different hoareAnnotationLocs

		}
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				freshToolKit.getManagedScript(), predicateFactory, mComputeHoareAnnotation, hoareAnnotationLocs);

		// make sure that mPref.getCfgSmtToolkit returns the worker toolkit
		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(getServices(), mPref, mInterpolationTechnique,
						mSimplificationTechnique, mXnfConversionTechnique, freshToolKit, predicateFactory, mIcfg);

		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs,
				mIcfg, predicateFactory, predicateFactoryInterpolantAutomata, mTransitionClazz);

		final ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(getServices(), mCounterexample,
				mInitialAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, mIteration),
				predicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				strategyType);

		// start worker
		return new CegarWorkerThread<L, A>(mLogger, mPref, mCounterexample, mAStarRandomHeuristicSeed, mResultBuilder,
				mCegarLoopBenchmark, iterationServices, freshToolKit, mStrategyFactory, mInitialAbstraction,
				predicateFactory, predicateFactoryInterpolantAutomata, stateFactoryForRefinement,
				mComputeHoareAnnotation, strategy, currentErrorLoc, mRootNode);
	}

	/*
	 * Parallel CEGAR loop of main thread
	 * In each iteration we pick a counterexample
	 * and setup a worker to check its feasibility
	 *
	 * The worker future contains either an interpolant or an error automaton.
	 *
	 * As soon as we obtain a worker result, we refine our abstraction.
	 * If abstraction is not empty, continue with the loop
	 * If no worker is done, continue with the loop
	 * If no thread is available and no worker is done we sleep
	 */
	@Override
	protected void iterate() throws AutomataLibraryException {
		// TODO manage time and timeout

		int runningThreads = 0;
		mActiveCounterexamples.add((NestedRun<L, IPredicate>) mCounterexample);
		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			boolean abstractionWasRefined = false;
			final boolean minimizePerWorker = true;
			try {
				mCegarLoopBenchmark.announceNextIteration();
				try {
					// can be null if no active test goals but threads are still running
					if (runningThreads < mThreadLimit && mCounterexample != null) {
						final IcfgLocation currentErrorLoc = getErrorLocFromCounterexample();
						final IUltimateServiceProvider iterationServices = createIterationTimer(currentErrorLoc);
						mServices = iterationServices;
						final RefinementStrategy strategyType = mPref.getRefinementStrategy(); // TODO parallel
																								// strategies
						final CegarWorkerThread<L, A> worker =
								setUpWorker(iterationServices, runningThreads, currentErrorLoc, strategyType);
						// worker is a Callable and is called here
						mECS.submit(worker);
						runningThreads += 1;
					} else {
						try {
							mLogger.info("All threads busy, going to sleep.");
							// No busy waiting via Completeable
							Future<WorkerThreadResult<L, A>> doneFuture = mECS.take(); // take doesnt remove the future
							mLogger.info("Waking up, a worker is done.");
							while (doneFuture != null) {
								try {
									final WorkerThreadResult<L, A> workerResult = doneFuture.get();
									mLogger.info("Main: A Thread is Done");
									runningThreads -= 1;
									workerResult.getAutomatonType();
									final List<L> trace = workerResult.getCounterexample().getWord().asList();
									final int traceHash = trace.hashCode();
									// TODO should be enough to save testgoal id right?
									final Integer testGoalId = mInActiveErrorLocs.get(traceHash);

									mLogger.info("Done TestGoal: " + testGoalId);
									mLogger.info("Done Type: " + workerResult.getAutomatonType());

									if (workerResult.getAutomatonType().equals(AutomatonType.FLOYD_HOARE)
											|| !useGoalSetForIsEmpty) {
										automataWaitingList.add(workerResult);
										// Free up the testgoal for counterexample search
										mInActiveErrorLocs.remove(traceHash);
									}

								} catch (final ExecutionException | InterruptedException e) {
									// TODO better handling of exceptions in worker thread
									e.printStackTrace();
									mExec.shutdownNow();
									throw new AutomataLibraryException(null, e.getMessage());
								}
								doneFuture = mECS.poll();
							}
						} catch (final InterruptedException e) {
							e.printStackTrace();
							mExec.shutdownNow();
							// TODO throw exception
						}
					}

					// Refine abstraction as long as there are automata in automataWaitingList
					while (!automataWaitingList.isEmpty()) {
						mLogger.info("Refining Abstraction: " + automataWaitingList.size());
						assert !automataWaitingList.isEmpty();
						final WorkerThreadResult<L, A> firstAutomatonInWaitingList = automataWaitingList.pop();
						if (useGoalSetForIsEmpty) {
							assert firstAutomatonInWaitingList.getAutomatonType().equals(AutomatonType.FLOYD_HOARE);
						}
						try {
							final INestedWordAutomaton<L, IPredicate> abstraction = mAbstraction;

							final List<L> trace = firstAutomatonInWaitingList.getCounterexample().getWord().asList();
							final int traceHash = trace.hashCode();
							mLogger.info("Subtrahend traceHash: " + traceHash);

							final Set<IcfgLocation> hoareAnnotationLocs;
							if (mComputeHoareAnnotation) {
								hoareAnnotationLocs = (Set<IcfgLocation>) TraceAbstractionUtils
										.getLocationsForWhichHoareAnnotationIsComputed(mRootNode,
												mPref.getHoareAnnotationPositions());
							} else {
								hoareAnnotationLocs = Collections.emptySet();
							}

							final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(
									getServices(), firstAutomatonInWaitingList.getWorkerMgdScript(),
									firstAutomatonInWaitingList.getPredicateFactory(), mComputeHoareAnnotation,
									hoareAnnotationLocs);

							final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff = computeAutomataDifference(
									abstraction, firstAutomatonInWaitingList, stateFactoryForRefinement);

							if (mPref.stopAfterFirstViolation()
									&& firstAutomatonInWaitingList.getAutomatonType() == AutomatonType.ERROR) {
								return;
							}
							mAbstraction = diff.getResult();
							if (minimizePerWorker) {
								minimizeAbstractionIfEnabled(stateFactoryForRefinement,
										new PredicateFactoryResultChecking(mPredicateFactory));

							}
							mActiveCounterexamples.remove(firstAutomatonInWaitingList.getCounterexample());
							// Kill the worker script
							((HistoryRecordingScript) firstAutomatonInWaitingList.getWorkerMgdScript().getScript())
									.exitWorkerOnly();
							abstractionWasRefined = true;
							// Not sure if necessary
							firstAutomatonInWaitingList.garbageCollect();
							assert !abstraction.equals(mAbstraction);
						} catch (final AssertionError ae) {
							// TODO it might happen that mCounterexample is no longer accepted
							mExec.shutdownNow();
							throw ae;
						}

					}

				} catch (AutomataOperationCanceledException | ToolchainCanceledException e) {
					// TODO deal with UNKNOWN
					throw e;
				}

				// Check if empty only if abstraction changed or we have a thread available
				if (abstractionWasRefined && !minimizePerWorker) {
					minimizeAbstractionIfEnabled(); // TODO warning uses NWA CEGAR loop
				} else {
					mIteration -= 1;
				}
				// need a new counterexample every iteration
				if (runningThreads < mThreadLimit) {
					// assert mActiveCounterexamples.size() == runningThreads;
					final IRun<L, ?> oldCounterexample = mCounterexample;
					final boolean isAbstractionCorrect = isAbstractionEmpty();

					if (oldCounterexample == mCounterexample) {
						System.out.println("Didnt Find a Counterexample!!! " + Thread.activeCount());
						mCounterexample = null;
					}
					if (mCounterexample != null) {
						resetThreadLimit();
						mActiveCounterexamples.add((NestedRun<L, IPredicate>) mCounterexample);
					} else {
						if (isAbstractionCorrect && runningThreads == 0) {
							assert isAbstractionCorrect == super.isAbstractionEmpty();
							mResultBuilder.addResultForAllRemaining(Result.SAFE);
							mExec.shutdownNow();
							return;
						}
					}
				}

			} finally {
				// TODO if (updateBudget) {
				// TODO final Set<String> destroyedStorables = getServices().getStorage().destroyMarker(msg);
			}

		}
		mExec.shutdownNow();
		mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);
	}

	private void resetThreadLimit() {
		mThreadLimit = mPref.getThreadLimit();
		if (mThreadLimit == 0) { // maximum of available cores
			mThreadLimit = Runtime.getRuntime().availableProcessors();
			mThreadLimit -= 1; // one for main thread
		}
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {

		if (mTestGeneration.equals(TestGenerationMode.None)) {
			// return super.isAbstractionEmpty();
		}
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		try {
			/*
			 * mActiveErrorLocs are all error locations that are available to our search
			 * (Not part of a counterexample that is currently checked by another thread)
			 * mActiveErrorLocs needs to be calculated in every iteration.
			 * Since mActiveErrorLocs must be subsetEq to getFinalStates()
			 * and getFinalStates() can change
			 */
			if (useGoalSetForIsEmpty) {
				mActiveErrorLocs.clear();

				for (final IPredicate testGoal : mAbstraction.getFinalStates()) {
					final ISLPredicate testGoalISL = (ISLPredicate) testGoal;
					final IAnnotations pLocAnno = testGoalISL.getProgramPoint().getPayload().getAnnotations()
							.get(TestGoalAnnotation.class.getName());
					if (mInActiveErrorLocs.containsValue(((TestGoalAnnotation) pLocAnno).mId)) {
						continue;
					} else {
						if (pLocAnno instanceof TestGoalAnnotation) {
							mActiveErrorLocs.add(testGoal);
						}
					}
				}
			}

			if (!useGoalSetForIsEmpty || mTestGeneration.equals(TestGenerationMode.None)) {
				mCounterexample = runWithModifiedGoalSet(mAbstraction, (Set<IPredicate>) mAbstraction.getFinalStates());
			} else {
				if (mActiveErrorLocs.isEmpty()) {
					mCounterexample = null;
					return true;
				}
				mCounterexample = runWithModifiedGoalSet(mAbstraction, mActiveErrorLocs);
				if (mCounterexample == null) {
					return true;
				}
				final List<?> sequence = mCounterexample.getStateSequence();
				final IPredicate currentGoal = (IPredicate) sequence.get(sequence.size() - 1);
				assert mActiveErrorLocs.contains(currentGoal);
				// mark test goal as busy/occupied
				final ISLPredicate testGoalISL = (ISLPredicate) currentGoal;
				final IAnnotations pLocAnno = testGoalISL.getProgramPoint().getPayload().getAnnotations()
						.get(TestGoalAnnotation.class.getName());
				final List<L> trace = mCounterexample.getWord().asList();
				final int traceHash = trace.hashCode();
				// use traceHash as identifier so we can calculate the identifier later
				mInActiveErrorLocs.put(traceHash, ((TestGoalAnnotation) pLocAnno).mId);
				// WARNING all goals can be in mInActiveErrorLocs, but we are not done yet!!
			}
			if (mCounterexample == null) {
				return true;
			} else {
				// For debugging only, can be used to test if the search returns redundant counterexamples
				final List<L> trace = mCounterexample.getWord().asList();
				final int traceHash = trace.hashCode();
				if (mAllCounterexamples.containsKey(traceHash)) {
					// if (useGoalSetForIsEmpty) {
					assert false;
					// }
					mCounterexample = null; // no assert false; because a thread can finish after difference before
											// isEmpty

				} else {
					mAllCounterexamples.put(traceHash, (NestedRun<L, IPredicate>) mCounterexample);
				}

			}

		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		}
		if (mCounterexample == null) {
			return true;
		}
		if (mPref.dumpAutomata()) {
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DumpTime);
			mDumper.dumpNestedRun(mCounterexample);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
		}
		mLogger.info("Found error trace");

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<L> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getMax());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}

		if (mPref.hasLimitTraceHistogram() && traceHistogram.getMax() > mPref.getLimitTraceHistogram()) {
			final String taskDescription =
					"bailout by trace histogram " + traceHistogram.toString() + " in iteration " + mIteration;
			throw new TaskCanceledException(UserDefinedLimit.TRACE_HISTOGRAM, getClass(), taskDescription);
		}

		return false;
	}

	@Override
	protected NestedRun<L, IPredicate> runWithModifiedGoalSet(final INestedWordAutomaton<L, IPredicate> abstraction,
			final Set<IPredicate> possibleEndPoints) throws AutomataOperationCanceledException {

		final boolean considerOnlyActive = false;
		if (mParallelSearchSrategy && considerOnlyActive) {
			return new IsEmpty<L, IPredicate>(new AutomataLibraryServices(mServices), abstraction,
					abstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints, false,
					IsEmpty.SearchStrategy.BFS, mActiveCounterexamples).getNestedRun();
		} else if (mParallelSearchSrategy && !considerOnlyActive) {
			final ArrayList<NestedRun<L, IPredicate>> allCounterexamples =
					new ArrayList<>(mAllCounterexamples.values());
			return new IsEmpty<L, IPredicate>(new AutomataLibraryServices(mServices), abstraction,
					abstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints, false,
					IsEmpty.SearchStrategy.BFS, allCounterexamples).getNestedRun();

		} else {
			return new IsEmpty<>(new AutomataLibraryServices(mServices), abstraction, abstraction.getInitialStates(),
					Collections.emptySet(), possibleEndPoints).getNestedRun();
		}

	}

	/*
	 * Difference is calculated twice first in worker and then in master.
	 * We need the worker CFG script here
	 */
	@SuppressWarnings("unchecked")
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend, final WorkerThreadResult<L, A> workerResult,
			final PredicateFactoryRefinement stateFactoryForRefinement)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");

			final PowersetDeterminizer<L, IPredicate> psd = new PowersetDeterminizer<>(workerResult.getSubtrahend(),
					true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			// TODO mStateFactoryForRefinement muss fresh vom worker script kommen

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
				final boolean notEnahncedInWorker = false; // TODO setting?
				if (workerResult.getEnhanceMode() != InterpolantAutomatonEnhancement.NONE && notEnahncedInWorker) {
					assert workerResult
							.getSubtrahend() instanceof AbstractInterpolantAutomaton : "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton<L>) workerResult.getSubtrahend()).switchToReadonlyMode();
				}
			}

			if (!workerResult.useErrorAutomaton()) {
				// TODO needs to get the worker counterexample
				// checkEnhancement(workerResult.getSubtrahendBeforeEnhancement(), workerResult.getSubtrahend());
			}
			// Future work:
			assert !mPref.dumpOnlyReuseAutomata();
			assert mFaultLocalizationMode == RelevanceAnalysisMode.NONE;

			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
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
					mIteration, predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION, mStoredRawInterpolantAutomata,
					mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac, lcsProvider, true);
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
				mHaf.updateOnMinimization(oldState2newState, newAbstraction);
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
			final PredicateFactory predicateFactory) {
		mSubtrahend = subtrahend;
		mAutomatonType = automatonType;
		mUseErrorAutomaton = useErrorAutomaton;
		mEnhanceMode = enhanceMode;
		mSubtrahendBeforeEnhancement = subtrahendBeforeEnhancement;
		mExploitSigmaStarConcatOfIa = explointSigmaStarConcatOfIA;
		mMgdScript = mgdScript;
		mCounterexample = counterexample;
		mPredicateFactory = predicateFactory;
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