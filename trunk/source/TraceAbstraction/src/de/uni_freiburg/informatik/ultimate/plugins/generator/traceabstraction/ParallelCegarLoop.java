package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.WorkerPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class ParallelCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {

	private final ArrayDeque<WorkerThreadResult<L, A>> automataWaitingList = new ArrayDeque<WorkerThreadResult<L, A>>();

	boolean mNoThreadFree;
	boolean mComputeHoareAnnotation;

	ExecutorService mExec;
	List<Future<WorkerThreadResult<L, A>>> mWorkerFutures;

	int mThreadLimit = 3; // Runtime.avalablecores or so
	CompletionService<WorkerThreadResult<L, A>> mECS;
	private final IIcfg<?> mRootNode;

	/**
	 *
	 * Compute Inital Abstraction, can be reused
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
		// TODO Auto-generated constructor stub

		// Start thread pool, TODO either fixed or not. try different sizes too
		mExec = Executors.newFixedThreadPool(mThreadLimit);
		// Holds the Future of each thread
		mWorkerFutures = new ArrayList<Future<WorkerThreadResult<L, A>>>();
		mRootNode = rootNode;
		mECS = new ExecutorCompletionService<>(mExec);
	}

	private CegarWorkerThread<L, A> setUpWorker(final IUltimateServiceProvider iterationServices,
			final int runningThreads, final IcfgLocation currentErrorLoc, final RefinementStrategy strategyType) {
		// mCsToolkit needs to give new mgdScript for each thread
		final CfgSmtToolkit freshToolKit = mCsToolkit.getCfgSmtToolkitWithFreshScript(iterationServices,
				getSolverSettings(iterationServices, mIteration + runningThreads + mCounterexample.hashCode() + "asd"));
		// Set the Main Script
		((HistoryRecordingScript) freshToolKit.getManagedScript().getScript())
				.setMainScript(mCsToolkit.getManagedScript());

		// Fill the map from worker tv to main tv so we can obtain boogievars later
		final Map<TermVariable, IProgramVar> varMap =
				((Boogie2SmtSymbolTable) mCsToolkit.getSymbolTable()).getSmtVar2ProgramVarMap();
		final TermTransferrer tf = new TermTransferrer(mCsToolkit.getManagedScript().getScript(),
				freshToolKit.getManagedScript().getScript());
		for (final TermVariable tv : varMap.keySet()) {
			((HistoryRecordingScript) freshToolKit.getManagedScript().getScript())
					.addTermVariableToMap((TermVariable) tf.transform(tv), tv);
		}

		/*
		 * Es ist so: predicateFactory bekommt entweder das main scrip
		 * Oder: Wir müssen uns darum kümmern, dass PredicateUnifier.getOrConstructPredicate etc. entsprechend transformieren
		 */
		final WorkerPredicateFactory predicateFactory =
				new WorkerPredicateFactory(mServices, freshToolKit.getManagedScript(), freshToolKit.getSymbolTable());

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
				mAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, mIteration),
				predicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				strategyType);

		// start worker
		return new CegarWorkerThread<L, A>(mLogger, mPref, mCounterexample, mAStarRandomHeuristicSeed, mResultBuilder,
				mCegarLoopBenchmark, iterationServices, freshToolKit, mStrategyFactory, mAbstraction, predicateFactory,
				predicateFactoryInterpolantAutomata, stateFactoryForRefinement, mComputeHoareAnnotation, strategy,
				currentErrorLoc, mRootNode);
	}

	/*
	 * CURRENT CEGAR SCHEME
	 *
	 * Initial Abstraction computeInitialAbstraction() -> isAbstractionEmpty()?
	 * -> No -> mCounterexample
	 ** Start of the Loop
	 *
	 * at the start of iterate() mCounterexample is already set and
	 *
	 * BasicCegarLoop.isCounterexampleFeasible()
	 * 	final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(...);
	 *  Strategy is for example CAMEL interpolate then fpbp	 *
	 *  Strategy gets the mCounterexample
	 *  Strategy contains an array of trace checks?? versthee ich nicht ganz
	 *
	 * 	final TraceAbstractionRefinementEngine<L> refinementEngine = new TraceAbstractionRefinementEngine<>(...);
	 *  Calculates feasibility??
	 *
	 *	mRefinementResult = refinementEngine.getResult();
	 *     Calls mRefinementResult.getCounterexampleFeasibility();
	 *
	 * returns a pair of Lbool and program execution
	 * Program execution is only relevant if SAT
	 *
	 * processFeasibilityCheckResult() has as parameter the feasibility and error location
	 * It returns the automaton type (and registers the result for the current error location)
	 *
	 *
	 *
	 * NWACegarLoop.refineAbstraction() computes automaton and calls:
	 * NWACegarLoop.computeAutomataDifference()
	 * Then mAbstraction is the difference
	 *
	 * NWACegarLoop.isAbstractionEmpty() searches a trace
	 * mCounterexample is the trace
	 *
	 ** End of the Loop
	 *
	 * PARRALLEL CEGAR
	 *
	 * Iterate over the automata storage.
	 * Compute the difference automaton starting with the first entry.
	 *
	 *
	 *
	 * Problem mCounterexample und mAbstraction must not change
	 */
	@Override
	protected void iterate() throws AutomataLibraryException {
		// TODO manage time and timeout

		boolean strategyCamelInUse = false;
		boolean strategyWolfInUse = false;
		int runningThreads = 0;

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			final IcfgLocation currentErrorLoc = getErrorLocFromCounterexample();
			final IUltimateServiceProvider parentServices = mServices;
			final IUltimateServiceProvider iterationServices = createIterationTimer(currentErrorLoc);
			mServices = iterationServices;
			final boolean updateBudget = true;
			boolean abstractionWasRefined = false;

			// TODO wait if all threads are busy
			try {
				mCegarLoopBenchmark.announceNextIteration();
				try {

					if (runningThreads < mThreadLimit) {

						RefinementStrategy strategyType;
						if (false) {
							strategyType = RefinementStrategy.WOLF;
							strategyWolfInUse = true;
							strategyCamelInUse = false;
						} else {// if (strategyWolfInUse) {
							strategyType = RefinementStrategy.CAMEL;
							strategyCamelInUse = true;
							strategyWolfInUse = false;
						}

						final CegarWorkerThread<L, A> worker =
								setUpWorker(iterationServices, runningThreads, currentErrorLoc, strategyType);

						final Future<WorkerThreadResult<L, A>> future = mECS.submit(worker);
						mWorkerFutures.add(future);
						runningThreads += 1;
					} else {

						try {
							mLogger.info("All threads busy, going to sleep.");
							mECS.take();
							mLogger.info("Waking up, a worker is done.");
						} catch (final InterruptedException e) {
							e.printStackTrace();
						}

					}

					final List<Future<WorkerThreadResult<L, A>>> doneThreads = new ArrayList<>();
					for (int i = 0; i < mWorkerFutures.size(); i++) {
						final Future<WorkerThreadResult<L, A>> futureResult = mWorkerFutures.get(i);
						try {
							if (futureResult.isDone()) {
								mLogger.info("Thread Done");
								runningThreads -= 1;
								automataWaitingList.add(futureResult.get());
								doneThreads.add(mWorkerFutures.get(i));
							}
						} catch (InterruptedException | ExecutionException e) {
							e.printStackTrace();
						}
					}
					mWorkerFutures.removeAll(doneThreads);

					while (!automataWaitingList.isEmpty()) {
						mLogger.info("Refining Abstraction: " + automataWaitingList.size());
						assert !automataWaitingList.isEmpty();
						final WorkerThreadResult<L, A> firstAutomatonInWaitingList = automataWaitingList.pop();
						try {
							final INestedWordAutomaton<L, IPredicate> abstraction = mAbstraction;

							// Set worker Script in CFG script

							// From this point on, CFG script term transfers everything
							// ((HistoryRecordingScript) firstAutomatonInWaitingList.getWorkerMgdScript().getScript())
							// .transferHistoryFromRecord(mCsToolkit.getManagedScript().getScript());

							// If we synchronize, the difference calculation will use main script which can lead to
							// concurrency problems
							// ((HistoryRecordingScript) firstAutomatonInWaitingList.getWorkerMgdScript().getScript())
							// .synchronizeWorkerAndMain();
							final List<L> trace = firstAutomatonInWaitingList.getCounterexample().getWord().asList();
							final int traceHash = trace.hashCode();
							mLogger.info("Subtrahend traceHash: " + traceHash);
							final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff =
									computeAutomataDifference(abstraction, firstAutomatonInWaitingList);

							if (mPref.stopAfterFirstViolation()
									&& firstAutomatonInWaitingList.getAutomatonType() == AutomatonType.ERROR) {
								return;
							}
							mAbstraction = diff.getResult();

							((HistoryRecordingScript) firstAutomatonInWaitingList.getWorkerMgdScript().getScript())
									.exitWorkerOnly();
							abstractionWasRefined = true;
							assert !abstraction.equals(mAbstraction);
						} catch (final AssertionError ae) {
							// TODO it might happen that mCounterexample is no longer accepted
							throw ae;
						}

					}

				} catch (AutomataOperationCanceledException | ToolchainCanceledException e) {
					// TODO deal with UNKNOWN
					throw e;
				}

				// Check if empty only if abstracion changed or we have a thread available
				if (abstractionWasRefined || (runningThreads < mThreadLimit)) { // TODO differenciate, if
																				// sheduleNewWorkerThread
					// but !abstractionWasRefined then other
					// counterexample
					minimizeAbstractionIfEnabled();
					final boolean isAbstractionCorrect = isAbstractionEmpty();
					if (isAbstractionCorrect) {
						mResultBuilder.addResultForAllRemaining(Result.SAFE);
						mExec.shutdown();
						return;
					}
				} else {
					mIteration -= 1;
				}
			} finally {
				// TODO if (updateBudget) {
				// TODO final Set<String> destroyedStorables = getServices().getStorage().destroyMarker(msg);
			}

		}
		mExec.shutdown();
		mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);
	}

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerThread() {

		automataWaitingList.add(null);
		return null;
	}

	/*
	 * difference is calculated by master thread
	 * needs to be done in loop
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend, final WorkerThreadResult<L, A> workerResult)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");

			final PowersetDeterminizer<L, IPredicate> psd = new PowersetDeterminizer<>(workerResult.getSubtrahend(),
					true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;

			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, workerResult.exploitSigmaStarConcatOfIa());
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(workerResult.getSubtrahend().size());

			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				throw tce;
			} finally {
				if (workerResult.getEnhanceMode() != InterpolantAutomatonEnhancement.NONE) {
					assert workerResult
							.getSubtrahend() instanceof AbstractInterpolantAutomaton : "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton<L>) workerResult.getSubtrahend()).switchToReadonlyMode();
				}
			}

			if (!workerResult.useErrorAutomaton()) {
				// TODO needs to get the worker counterexample
				// checkEnhancement(workerResult.getSubtrahendBeforeEnhancement(), workerResult.getSubtrahend());
			}

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
}

final class WorkerThreadResult<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mSubtrahend;
	private final AutomatonType mAutomatonType;
	private final boolean mUseErrorAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mSubtrahendBeforeEnhancement;
	private final InterpolantAutomatonEnhancement mEnhanceMode;
	private final boolean mExploitSigmaStarConcatOfIa;
	private final ManagedScript mMgdScript;
	private final IRun<L, ?> mCounterexample;

	/**
	 * @param automatonType
	 *
	 *
	 */
	WorkerThreadResult(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final InterpolantAutomatonEnhancement enhanceMode, final boolean useErrorAutomaton,
			final AutomatonType automatonType, final ManagedScript mgdScript, final IRun<L, ?> counterexample) {
		mSubtrahend = subtrahend;
		mAutomatonType = automatonType;
		mUseErrorAutomaton = useErrorAutomaton;
		mEnhanceMode = enhanceMode;
		mSubtrahendBeforeEnhancement = subtrahendBeforeEnhancement;
		mExploitSigmaStarConcatOfIa = explointSigmaStarConcatOfIA;
		mMgdScript = mgdScript;
		mCounterexample = counterexample;
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
}