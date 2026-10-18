/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.IInvariantSink;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantSupplier;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.kinduction.KInductionWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;

public class ParallelNwaCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {

	final String mDestroyEverything = "destroyEverything";

	/** z3's value of :timeout for no timeout at all. */
	private static final long Z3_NO_TIMEOUT = 4294967295L;

	/**
	 * Stack size of the worker threads. The JVM default is far too small for the recursive parts of the workers, e.g.
	 * k-induction's counterexample reconstruction on a long run through recursive procedures, or its path expression
	 * visitor on a deeply nested regex.
	 */
	private static final long WORKER_STACK_SIZE_BYTES = 256L * 1024 * 1024;

	/**
	 * The per-check timeout option of the external solvers we can configure, by the name of their executable: the
	 * pattern matches the option as it may already appear in the configured command, the format string writes a new
	 * one. Mirrors {@link SolverBuilder.ExternalSolver}, which spells the same options for its built-in commands.
	 */
	private static final Map<String, Entry<Pattern, String>> SOLVER_TIMEOUT_OPTION = Map.of(
			"z3", Map.entry(Pattern.compile("\\s*-t:\\d+"), " -t:%d"),
			"cvc4", Map.entry(Pattern.compile("\\s*--tlimit-per=\\d+"), " --tlimit-per=%d"),
			"cvc5", Map.entry(Pattern.compile("\\s*--tlimit-per=\\d+"), " --tlimit-per=%d"),
			// -t and --time-limit are bitwuzla's limit for the whole run, not per check, so they stay.
			"bitwuzla", Map.entry(Pattern.compile("\\s*(?:-T\\s*|--time-limit-per[=\\s]+)\\d+"),
					" --time-limit-per=%d"));

	// Parallel Setup
	private final ExecutorService mExec;
	private final int mThreadLimit;
	private final int mNumTaWorkers;
	private final int mNumKInductionWorkers;
	private int mRunningThreads = 0;
	// Workers that finished without a verdict. They are gone from the pool and will produce nothing more.
	private int mRetiredWorkers = 0;
	// Collects invariants from the TA workers for the k-induction workers. Null unless there is a
	// k-induction worker and someone to feed it; runs on mInvariantExec, outside the worker pool, since it never
	// decides the program.
	private InvariantSupplier<L, A> mInvariantSupplier;
	private ExecutorService mInvariantExec;
	// Set before the workers are shut down and their solvers destroyed: a query failing from then on is no crash.
	private volatile boolean mShuttingDown;

	// private final CompletionService<WorkerThreadResult<L, A>> mECS;
	BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue = new LinkedBlockingQueue<>();
	BlockingQueue<WorkerThreadResult<L, A>> mWorkerResultQueue = new LinkedBlockingQueue<>();

	// need global program cache, but worker need to get copy otherwise we
	// synchronize
	private final PathProgramCache<L> mProgramCache = new PathProgramCache<>(mLogger);

	// Strategies
	public final HashMap<Integer, NestedRun<L, ?>> mActiveCounterexamples = new HashMap<>();
	private final Set<Integer> mCounterexamplesToBeRemovedFromActiveCexMap = new HashSet<>();
	protected InterpolationTechnique mInterpolationTechnique;

	public Class<L> mTransitionClazz;

	// Addtional Statistiks for Evaluation
	private Integer mCounterexamplesChecked = 0;
	private Integer mRefinementsDone = 0;
	private final Integer mCountTimeoutsInSearch = 0;
	private final Integer mCountFailedRunConstructions = 0;
	private Integer mCountFailedToFindCex = 0;
	private Integer mCountBfsFoundCex = 1;
	private final Integer mCountIsEmptyParallel = 0;
	private Integer maxActiveThreads = 0;
	private final Integer mActiveExecutors = 0;
	private long mSearchTime = 0;
	private long mWorkerSetUpTime = 0;
	private int mIterationsWithMaxThreads = 0;
	private int mIterationsWithOneThread = 0;
	private final int mExceptionInWorker = 0;

	private long mRefinementTime = 0;
	private long mIdleTime = 0;

	// Moves the states of the workers' automata into the main script; null unless we compute a proof.
	private final WorkerStateTransferrer<L> mStateTransferrer;

	// The ICFG as it was before the workers started, see detachTransferredEdges
	private final Set<IcfgLocation> mOriginalLocations;
	private final Set<IcfgEdge> mOriginalEdges;
	private static final long WORKER_TERMINATION_TIMEOUT_SECONDS = 10;

	/**
	 * Based on the @NwaCegarLoop. Given a ThreadLimit, creates a ExecutionerService that will manage the worker
	 * threads. Executes each tracecheck in a new thread called worker. This loop, only searches for counterexamples and
	 * updates the abstraction. The feasiblity check and generalization of interpolant automata is done by the workers.
	 * TODO option to save memory, measure heap, then dont spawn worker / kill a worker
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */

	public ParallelNwaCegarLoop(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		// Start thread pool
		if (mPref.getThreadLimit() == 0) { // maximum of available cores
			mNumTaWorkers = Runtime.getRuntime().availableProcessors() - 1; // one for main thread
		} else {
			mNumTaWorkers = mPref.getThreadLimit();
		}
		mNumKInductionWorkers = mPref.getNumKInductionWorkers();
		mThreadLimit = mNumTaWorkers + mNumKInductionWorkers;
		if (mThreadLimit == 0) {
			throw new AssertionError("At least one parallel CEGAR worker thread must be configured");
		}
		if (mProofUpdater != null) {
			if (mPref.differenceSenwa()) {
				throw new UnsupportedOperationException(
						"Computing a Hoare annotation in the parallel CEGAR loop requires the NWA difference, not SENWA");
			}
			mStateTransferrer = new WorkerStateTransferrer<>(new AutomataLibraryServices(services),
					csToolkit.getManagedScript(), predicateFactory);
		} else {
			mStateTransferrer = null;
		}
		mOriginalLocations = collectLocations(rootNode);
		// By identity: a transferred copy keeps the serial number, i.e., the hash code, of its original.
		mOriginalEdges = Collections.newSetFromMap(new IdentityHashMap<>());
		mOriginalLocations.forEach(loc -> mOriginalEdges.addAll(loc.getOutgoingEdges()));

		mExec = Executors.newFixedThreadPool(mThreadLimit, workerThreadFactory("Cegar Worker"));
		Thread.currentThread().setName("Main Cegar Thread");
		getServices().getStorage().pushMarker(mDestroyEverything);
	}

	private static ThreadFactory workerThreadFactory(final String name) {
		final AtomicInteger counter = new AtomicInteger();
		return runnable -> new Thread(null, runnable, name + " " + counter.incrementAndGet(),
				WORKER_STACK_SIZE_BYTES);
	}

	/*
	 * Parallel CEGAR loop. In each iteration we pick a counterexample and put it into a blocking queue for a worker to
	 * check its feasibility
	 **
	 * As soon as we obtain a worker result via blocking queue, we refine our abstraction. If abstraction is not empty,
	 * we continue with the loop. If no worker is done, continue with the loop. If no thread is available and no worker
	 * is done we sleep.
	 */
	@Override
	protected void iterate() throws AutomataLibraryException {
		try {
			iterateWithWorkers();
		} finally {
			// Not every way out of the loop shuts the pool down, but the supplier would wait for messages forever.
			mShuttingDown = true;
			if (mInvariantExec != null) {
				mInvariantExec.shutdownNow();
			}
		}
	}

	/**
	 * @return whether the loop is done, so that a worker whose solver is destroyed under a query stops quietly
	 */
	public boolean isShuttingDown() {
		return mShuttingDown;
	}

	private void iterateWithWorkers() throws AutomataLibraryException {
		// TODO manage time and timeout
		boolean didntFindCexLastIteration = false;
		setUpWorkerThreads();
		// start worker for initial cex:
		startWorker();

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			abortIfTimeout();
			boolean abstractionWasRefined = false;
			mLogger.info(String.format("=== Iteration %s ===", getIteration()));

			// we sleep if not: thread or counterexample is available
			final WorkerThreadResult<L, A> workerResult = getWorkerResult(didntFindCexLastIteration);
			if (workerResult != null) {
				final int refinementsBefore = mRefinementsDone;
				final boolean terminate = handleWorkerResults(workerResult);
				if (terminate) {
					return;
				}
				// Results without a verdict retire their worker but leave the abstraction as it is, which may still be
				// the initial one: minimization rejects that for interprocedural programs (not an IDoubleDecker).
				abstractionWasRefined = mRefinementsDone > refinementsBefore;
			}

			if (abstractionWasRefined && !mPref.minimizeAbstractionPerWorker()) {
				// uses NWA CEGAR loop
				// When do we minimize how often?
				minimizeAbstractionIfEnabled();
			}
			if (abstractionWasRefined) {
				// If we didnt find one we wait until we refine the abstraction
				didntFindCexLastIteration = false;
			}

			/*
			 * In the first iteration we search via BFS, then we use IsEmptyParallel
			 */
			boolean firstIteration = true;
			while (mRunningThreads < mThreadLimit && !didntFindCexLastIteration) {
				assert mRunningThreads >= 0;
				mCounterexample = searchForErrorTrace(!firstIteration);
				if (mCounterexample == null) {
					didntFindCexLastIteration = true;
					break;
				}
				if (mCounterexample != null) {
					startWorker();
				}
				firstIteration = false;
			}
			updateAndPrintStatistics(false);
		}
		mExec.shutdownNow();
		mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);

	}

	/*
	 * returns true, if CEGAR should terminate.
	 */
	private boolean handleWorkerResults(final WorkerThreadResult<L, A> firstWorkerResult)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		WorkerThreadResult<L, A> workerResult = firstWorkerResult;
		// go through all done workerResult
		while (workerResult != null) {
			final long time = System.nanoTime() / 1000000000;

			mLogger.info("Main: A Thread is Done");
			if (workerResult.workerCrashed()) {
				mLogger.error("Main: Worker Crashed! exiting CEGAR loop.");
				// TODO we can try to recover, and restart the worker.
				// It might be that just this counterexample crashes our worker and we can still prove the
				// program correct
				shutDownAndDestroy(mDestroyEverything);
				throw new AssertionError("Worker Crashed!, Exiting CEGAR loop!");
			}
			// A worker that ran to completion without deciding the program (the solver answered unknown). It has
			// nothing to refine with, so the only thing to do is retire it and let the remaining workers finish.
			// If it was the last one, nobody is left to decide and the honest answer is UNKNOWN - not a crash.
			if (workerResult.noVerdict()) {
				mRetiredWorkers += 1;
				mLogger.warn("Main: %s finished without a verdict (%d of %d worker(s) retired)",
						workerResult.getWorkerType(), mRetiredWorkers, mThreadLimit);
				if (mRetiredWorkers >= mThreadLimit) {
					mLogger.warn("Main: every worker finished without a verdict, reporting UNKNOWN");
					mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
					shutDownAndDestroy(mDestroyEverything);
					updateAndPrintStatistics(true);
					return true;
				}
				workerResult = mWorkerResultQueue.poll();
				continue;
			}
			// A whole-program worker that refuted the program has already registered UNSAFE on mResultBuilder. It
			// has no subtrahend and no error automaton, so there is nothing to refine with. This must be checked
			// BEFORE the safe sentinel below, which a refutation would otherwise match (it too has no subtrahend)
			// and be reported as SAFE.
			if (workerResult.getAutomatonType() == AutomatonType.ERROR
					&& workerResult.mWorkerType.equals(WorkerType.KINDUCTION)) {
				mLogger.info("Main: %s refuted the program", workerResult.mWorkerType);
				// Fills only the error locations that have no result yet; the refuted one keeps its UNSAFE.
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
				shutDownAndDestroy(mDestroyEverything);
				updateAndPrintStatistics(true);
				return true;
			}
			// K-induction proves the whole program safe at once, it has no subtrahend to
			// refine with. The null automaton type is what distinguishes that sentinel from the refutation above.
			if (workerResult.mWorkerType.equals(WorkerType.KINDUCTION)
					&& (workerResult.getSubtrahend() == null) && (workerResult.getAutomatonType() == null)) {
				if (mProofUpdater != null) {
					useKInductionProof(workerResult);
				}
				mAbstraction = new NestedWordAutomaton(new AutomataLibraryServices(getServices()),
						mAbstraction.getVpAlphabet(), mPredicateFactoryInterpolantAutomata);
				mResultBuilder.addResultForAllRemaining(Result.SAFE);
				updateAndPrintStatistics(true);
				return true;
			}
			// If Error automaton terminate immediately
			if (mPref.stopAfterFirstViolation() && workerResult.getAutomatonType() == AutomatonType.ERROR) {
				shutDownAndDestroy(mDestroyEverything);
				updateAndPrintStatistics(true);
				return true;
			}

			mLogger.info("Worker Automaton Type: " + workerResult.getAutomatonType());
			mLogger.info("Refining Abstraction");
			refinement(workerResult);
			mRefinementsDone += 1;

			// Not sure if necessary
			workerResult.garbageCollect();
			// If new abstraction is empty terminate immediately
			if (isSafeThenTerminate()) {
				updateAndPrintStatistics(true);
				return true;
			}
			workerResult = mWorkerResultQueue.poll();
			mRefinementTime += ((System.nanoTime() / 1000000000) - time);
		}
		mLogger.info("No more worker results to process");
		assert workerResult == null;
		return false;
	}

	/**
	 * Makes the invariants of a k-induction proof the proof of this loop. Without them, or if they do not fit the ICFG,
	 * the proof is an annotation without any invariant, i.e. a trivial correctness witness.
	 * <p>
	 * It must not be extracted from the abstraction: k-induction proves the program while the abstraction is still
	 * being refined, so the Hoare annotation fragments of the refinements so far are incomplete, and extracting them
	 * from the abstraction we replace by an empty one annotates loop heads with {@code false}.
	 */
	private void useKInductionProof(final WorkerThreadResult<L, A> workerResult) {
		final Map<IPredicate, IPredicate> annotation = kInductionAnnotation(workerResult);
		if (annotation == null) {
			mProofUpdater.setProof(Collections.emptyMap());
			return;
		}
		mLogger.info("Main: using the invariants of the k-induction proof at %d loop head(s)", annotation.size());
		mProofUpdater.setProof(annotation);
	}

	/**
	 * @return the invariants of a k-induction proof as an annotation of the initial abstraction, or null if there are
	 *         none or they do not fit the ICFG
	 */
	private Map<IPredicate, IPredicate> kInductionAnnotation(final WorkerThreadResult<L, A> workerResult) {
		final Map<IPredicate, Term> invariants = workerResult.getProofInvariants();
		if (invariants == null) {
			mLogger.info("Main: k-induction proof without invariants, the correctness witness has none");
			return null;
		}
		// The witness reports invariants at the ICFG's loop locations; k-induction finds its loop heads itself.
		final Set<IcfgLocation> loopLocations = new HashSet<>(mIcfg.getLoopLocations());
		final Map<IPredicate, IPredicate> annotation = new HashMap<>();
		for (final Map.Entry<IPredicate, Term> entry : invariants.entrySet()) {
			final IcfgLocation loc = ((ISLPredicate) entry.getKey()).getProgramPoint();
			if (!loopLocations.remove(loc) || !mProofUpdater.getProgram().getStates().contains(entry.getKey())) {
				mLogger.warn("Main: k-induction loop head %s is no loop location of the ICFG, the correctness witness "
						+ "has no invariants", loc);
				return null;
			}
			annotation.put(entry.getKey(), mPredicateFactory.newSPredicate(loc,
					mStateTransferrer.transferTerm(entry.getValue(), workerResult.getWorkerMgdScript())));
		}
		if (!loopLocations.isEmpty()) {
			mLogger.warn("Main: k-induction has no loop head at the loop location(s) %s, the correctness witness has "
					+ "no invariants", loopLocations);
			return null;
		}
		return annotation;
	}

	private void setUpWorkerThreads() {
		final IcfgLocation currentErrorLoc = getErrorLocFromCounterexample();
		final IUltimateServiceProvider iterationServices = createIterationTimer(currentErrorLoc);
		int id = 0;
		try {
			// The supplier's channels must exist before any worker that feeds or reads them.
			final TransferBetweenMainAndWorker<L, IPredicate> invariantTransfer;
			if (needsInvariantSupplier()) {
				invariantTransfer = new TransferBetweenMainAndWorker<>(new AutomataLibraryServices(mServices), mLogger,
						mCsToolkit.getManagedScript(), iterationServices,
						getSolverSettings(WorkerType.INVARIANT, "InvariantSupplier"), mCsToolkit,
						freshVarPrefix(WorkerType.INVARIANT, id));
				mInvariantSupplier = new InvariantSupplier<>(mLogger, iterationServices,
						invariantTransfer.getWorkerCfgSmtToolKit(), mWorkerResultQueue, this::isShuttingDown,
						probationSettings());
			} else {
				invariantTransfer = null;
			}
			if (mInvariantSupplier != null) {
				mInvariantSupplier.setAbstraction(transferForInvariantSupplier(invariantTransfer));
				mInvariantExec = Executors.newSingleThreadExecutor(workerThreadFactory("Invariant Supplier"));
				mInvariantExec.submit(mInvariantSupplier);
			}
			for (int i = 0; i < mNumTaWorkers; i++) {
				mExec.submit(setUpWorkerThread(iterationServices, id, WorkerType.TA));
				id++;
			}
			for (int i = 0; i < mNumKInductionWorkers; i++) {
				mExec.submit(setUpWorkerThread(iterationServices, id, WorkerType.KINDUCTION));
				id++;
			}
		} catch (final InterruptedException e) {
			throw new AssertionError("Interrupted during worker setup " + e);
		}
	}

	/**
	 * The prefix the worker's {@link ManagedScript} puts into every variable it mints.
	 * <p>
	 * {@code CfgSmtToolkit#createFreshManagedScript} replays the main script's whole declaration history onto the
	 * worker script, including the constants the main thread declared for its own auxiliary variables, while the
	 * worker's {@link ManagedScript} starts its per-basename counter at zero. The k-induction worker composes tens of
	 * thousands of transition formulas while it builds its loop tree, so its counter reliably reaches an index the
	 * main thread already used and the aux-var constant is rejected as "already defined". A prefix that is unique per
	 * worker keeps the two name spaces apart.
	 * <p>
	 * Only k-induction gets one: the other worker types never came close to the collision, and an empty prefix keeps
	 * their variable names exactly as they were.
	 */
	private static String freshVarPrefix(final WorkerType workerType, final int id) {
		switch (workerType) {
		case KINDUCTION:
			return "ki" + id + "_";
		case INVARIANT:
			// Builds the same loop tree as k-induction, so it is exposed to the same collision.
			return "inv_";
		default:
			return "";
		}
	}

	/**
	 * Only k-induction consumes invariants, the TA workers produce them.
	 */
	private boolean needsInvariantSupplier() {
		return mNumKInductionWorkers > 0 && interpolantsFeedInvariantSupplier();
	}

	private boolean interpolantsFeedInvariantSupplier() {
		return mNumTaWorkers > 0 && mPref.submitInterpolantInvariants();
	}

	private IInvariantSink invariantSink(final boolean enabled) {
		return mInvariantSupplier == null || !enabled ? IInvariantSink.none() : mInvariantSupplier.sink();
	}

	/**
	 * The initial abstraction, as an automaton of the invariant supplier's script.
	 */
	private INestedWordAutomaton<L, IPredicate>
			transferForInvariantSupplier(final TransferBetweenMainAndWorker<L, IPredicate> transfer) {
		final CfgSmtToolkit toolkit = transfer.getWorkerCfgSmtToolKit();
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, toolkit.getManagedScript(), toolkit.getSymbolTable());
		final PredicateFactoryForInterpolantAutomata emptyStackFactory =
				new PredicateFactoryForInterpolantAutomata(toolkit.getManagedScript(), predicateFactory, false);
		return (INestedWordAutomaton<L, IPredicate>) transfer.transferAutomaton(mAbstraction, emptyStackFactory,
				TransferMode.MAIN2WORKER);
	}

	/*
	 * Sets up a worker that communicates via blocking queues and stays alive after one counterexample check. Every
	 * transfer between controller and worker goes via @TransferBetweenMainAndWorker.
	 */
	private ICegarNwaWorkerThread<L, A> setUpWorkerThread(final IUltimateServiceProvider iterationServices,
			final int id, final WorkerType workerType) throws InterruptedException {
		final TransferBetweenMainAndWorker<L, IPredicate> transferUtils = new TransferBetweenMainAndWorker<>(
				new AutomataLibraryServices(mServices), mLogger, mCsToolkit.getManagedScript(), iterationServices,
				getSolverSettings(workerType,
						getIteration() + mRunningThreads + mCounterexample.getWord().asList().hashCode() + "parallel"),
				mCsToolkit, freshVarPrefix(workerType, id));

		final CfgSmtToolkit freshToolKit = transferUtils.getWorkerCfgSmtToolKit();

		// Create predicateFactory with worker script
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, freshToolKit.getManagedScript(), freshToolKit.getSymbolTable());

		// The worker's factories never preserve terms, even if we compute a proof: the states of the abstraction a
		// worker gets are predicates of the main script, which the worker must not conjoin with its own. The Hoare
		// annotation is built by the main thread alone, after it moved the worker's states into its script.
		final boolean computeProof = mProofUpdater != null;
		final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata =
				new PredicateFactoryForInterpolantAutomata(freshToolKit.getManagedScript(), predicateFactory, false);
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				freshToolKit.getManagedScript(), predicateFactory, false, Collections.emptySet());

		// make sure that mPref.getCfgSmtToolkit returns the worker toolkit
		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(getServices(), mPref, mInterpolationTechnique,
						mSimplificationTechnique, freshToolKit, predicateFactory, mIcfg);

		switch (workerType) {
		case KINDUCTION:
			return new KInductionWorkerThread<>(mLogger, mPref, id, mResultBuilder, iterationServices, freshToolKit,
					predicateFactory, taCheckAndRefinementPrefs, predicateFactoryInterpolantAutomata,
					stateFactoryForRefinement, computeProof, this, mWorkerResultQueue, mWorkerTaskQueue,
					transferUtils, mTaskIdentifier, mInvariantSupplier == null ? IInvariantSupplier.none()
							: mInvariantSupplier.subscribe(freshToolKit.getManagedScript()));
		case TA:
			return new CegarNwaWorkerThread<>(mLogger, mPref, id, mResultBuilder, iterationServices, freshToolKit,
					predicateFactory, taCheckAndRefinementPrefs, predicateFactoryInterpolantAutomata,
					stateFactoryForRefinement, computeProof, this, mWorkerResultQueue, mWorkerTaskQueue,
					transferUtils, invariantSink(interpolantsFeedInvariantSupplier()));
		default:
			throw new AssertionError("Unknown worker type " + workerType);
		}
	}

	private void updateAndPrintStatistics(final boolean printStatistics) {

		if (mRunningThreads > maxActiveThreads) {
			maxActiveThreads = mRunningThreads;
		}
		if (mRunningThreads == mThreadLimit) {
			mIterationsWithMaxThreads += 1;
		}
		if (mRunningThreads == 1) {
			mIterationsWithOneThread += 1;
		}
		if (printStatistics) {
			mLogger.info("Iteration " + getIteration());
			mLogger.info("Refinements: " + mRefinementsDone);
			mLogger.info("Counterexamples: " + mCounterexamplesChecked);
			mLogger.info("SearchTimeout: " + mCountTimeoutsInSearch);
			mLogger.info("RunConstructionFailed: " + mCountFailedRunConstructions);
			mLogger.info("SearchFailed: " + mCountFailedToFindCex);
			mLogger.info("BFS: " + mCountBfsFoundCex);
			mLogger.info("IsEmptyParallel: " + mCountIsEmptyParallel);
			mLogger.info("ActiveThreads: " + maxActiveThreads);
			mLogger.info("ActiveExecutorsForPathPrograms: " + mActiveExecutors);
			mLogger.info("IterationsWithMaxThreads: " + mIterationsWithMaxThreads);
			mLogger.info("IterationsWithONEThread: " + mIterationsWithOneThread);
			mLogger.info("SearchTime: " + mSearchTime + " s");
			mLogger.info("WorkerSetUpTime: " + mWorkerSetUpTime + " s");
			mLogger.info("ExceptionInWorker: " + mExceptionInWorker);
			mLogger.info("mRefinementTime: " + mRefinementTime);
			mLogger.info("IdleTime: " + mIdleTime);
		}
	}

	private boolean isSafeThenTerminate() throws AutomataOperationCanceledException {
		// If IsEmpty says its empty, then we can terminate even if threads are still
		// running
		mLogger.info("Checking if program is safe");
		if (super.isAbstractionEmpty() || mAbstraction.size() == 0) {
			mResultBuilder.addResultForAllRemaining(Result.SAFE);
			shutDownAndDestroy(mDestroyEverything);
			return true;
		}
		// set cex to null to be certain we dont check counterexamples from the old
		// abstraction (super.isAbstractionEmpty() will set mCounterexample)
		mCounterexample = null;
		return false;
	}

	/*
	 * When we reach this method, we will always start at least one new worker.
	 */
	private void startWorker() {
		final WorkerThreadTask<L> task = new WorkerThreadTask<>(mCounterexample);
		mProgramCache.addRun(mCounterexample.getWord());
		task.setPathProgramCount(mProgramCache.getPathProgramCount(mCounterexample.getWord()));
		mWorkerTaskQueue.add(task);
		final long time = System.nanoTime() / 1000000000;
		mLogger.info("Main: Starting Thread");
		final IcfgLocation currentErrorLoc = getErrorLocFromCounterexample();
		final IUltimateServiceProvider iterationServices = createIterationTimer(currentErrorLoc);
		mServices = iterationServices;
		mRunningThreads += 1;
		mCounterexamplesChecked += 1;
		// add mCounterexample to list such that we dont get it twice in our search
		addCounterexampleToSet((NestedRun<L, ?>) mCounterexample);
		mWorkerSetUpTime += ((System.nanoTime() / 1000000000) - time);
	}

	private WorkerThreadResult<L, A> getWorkerResult(final boolean didntFindCexLastIteration) {
		WorkerThreadResult<L, A> doneFuture = null;

		if (mRunningThreads >= mThreadLimit || didntFindCexLastIteration) {
			assert mRunningThreads > 0;
			mLogger.info("All threads busy, going to sleep.");
			// No busy waiting via BlockingQueue
			final long time = System.nanoTime() / 1000000000;
			try {
				doneFuture = mWorkerResultQueue.take();
			} catch (final InterruptedException e) {
				throw new AssertionError("Main was Interrupted while waiting for results: " + e);
			}
			mIdleTime += ((System.nanoTime() / 1000000000) - time);
			mLogger.info("Waking up, a worker is done.");
		} else {
			doneFuture = mWorkerResultQueue.poll();
		}
		return doneFuture;
	}

	private void shutDownAndDestroy(final Object marker) {
		mShuttingDown = true;
		mExec.shutdownNow();
		if (mInvariantExec != null) {
			mInvariantExec.shutdownNow();
		}
		final Set<String> destroyedStorables = getServices().getStorage().destroyMarker(marker);
		if (!destroyedStorables.isEmpty()) {
			mLogger.warn("Destroyed unattended storables created during the last iteration: "
					+ destroyedStorables.stream().collect(Collectors.joining(",")));
		}
	}

	private void refinement(final WorkerThreadResult<L, A> threadResult)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		// mInterations equals the amount of refinements
		mCegarLoopBenchmark.announceNextIteration();

		removeCounterexampleFromSet(threadResult.getCounterexample());

		// The states of the main abstraction have to come from the main loop's own factory. Each worker has a fresh
		// predicate factory whose serial numbers start at 1 again, so states of different workers would share serial
		// numbers in one automaton, which UnknownState.equals rejects. If we compute a proof, the factory conjoins the
		// states of the abstraction with those of the subtrahend, so these must be predicates of the main script.
		final PredicateFactoryRefinement stateFactoryForRefinement = mStateFactoryForRefinement;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		if (mStateTransferrer == null) {
			subtrahend = threadResult.getSubtrahend();
		} else {
			subtrahend = mStateTransferrer.transferStates(threadResult.getSubtrahend(),
					threadResult.getWorkerMgdScript(), mPredicateFactoryInterpolantAutomata);
		}
		mLogger.info("Difference in Main");
		final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff = computeAutomataDifference(mAbstraction, subtrahend,
				threadResult, stateFactoryForRefinement);

		mAbstraction = diff.getResult();

		if (mPref.minimizeAbstractionPerWorker()) {
			minimizeAbstractionIfEnabled();
		}
		mRunningThreads -= 1;
		mLogger.info("Main: Refinement done.");
	}

	/*
	 * Only add a counterexample if it is being checked by a thread otherwise we are unsound
	 */
	private void addCounterexampleToSet(final NestedRun<L, ?> counterexample) {
		final List<L> trace = counterexample.getWord().asList();
		final int traceHash = trace.hashCode();
		if (mActiveCounterexamples.containsKey(traceHash)) {
			throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
		}
		mActiveCounterexamples.put(traceHash, counterexample);
	}

	/*
	 * OnlyActive means only countereamples actively being checked by workers. The alternative is all previously found
	 * counterexamples.
	 */
	private void removeCounterexampleFromSet(final IRun<L, ?> cex) {
		final List<L> trace = cex.getWord().asList();
		final int traceHash = trace.hashCode();
		mLogger.info("Subtrahend traceHash: " + traceHash);
		// Only remove after the counterexample is no longer in the abstraction
		if (mPref.considerOnlyActiveCounterexamplesInIsEmptyParallel()) {
			mActiveCounterexamples.remove(traceHash);
		} else {
			if (mCounterexamplesToBeRemovedFromActiveCexMap == null) {
				return;
			}
			mCounterexamplesToBeRemovedFromActiveCexMap.add(traceHash);
		}
	}

	/*
	 * The worker using this method to get the Abstraction need to ensure, they use the @TransferBetweenMainAndWorker To
	 * transfer the abstraction to their cfgscript. Worker may only use this to read-only access the abstraction!
	 */
	public INestedWordAutomaton<L, IPredicate> getAbstraction() {
		return mAbstraction;
	}

	private IsEmpty<L, IPredicate> getSearch(final IsEmpty.SearchStrategy strategy,
			final Set<IPredicate> possibleEndPoints) throws AutomataOperationCanceledException {
		switch (strategy) {
		case PARALLEL:
			return new IsEmptyParallel<>(new AutomataLibraryServices(mServices), mAbstraction,
					mAbstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints,
					possibleEndPoints == null, IsEmpty.SearchStrategy.BFS, mActiveCounterexamples,
					mPref.getSearchLoopBound());
		default:
			return new IsEmpty<>(new AutomataLibraryServices(getServices()), mAbstraction, strategy);
		}
	}

	// If search was BFS, the counterexample might not be fresh.
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
			if (mActiveCounterexamples.containsKey(traceHash)) {
				fresh = false;
			}
			return correct && fresh;
		}
		return false;
	}

	/*
	 * Search for an error trace in the current mAbstraction. First time with a new abstraction we try BFS, then
	 * IsEmptyParallel
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace(final boolean onlyDoIsEmptyParallel)
			throws AutomataOperationCanceledException {
		final long time = System.nanoTime() / 1000000000;
		final Set<IPredicate> possibleEndPoints = null;

		IsEmpty<L, IPredicate> search;
		if (!onlyDoIsEmptyParallel) {
			search = getSearch(IsEmpty.SearchStrategy.BFS, possibleEndPoints);
			if (isSearchCorrectAndTraceFresh(search)) {
				mCountBfsFoundCex += 1;
				mLogger.info("Found new Counterexample via BFS!");
				return search.getNestedRun();
			}
		}
		search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.info("Found new Counterexample via IsEmptyParallel!");
			return search.getNestedRun();
		}
		mLogger.info("Did not Find a Counterexample!");
		mCountFailedToFindCex += 1;
		assert mRunningThreads > 0;

		mSearchTime += ((System.nanoTime() / 1000000000) - time);
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
	 * Difference is calculated twice first in worker and then in master. All automata obtained from the worker need to
	 * be transferred to the master cfg script!
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final WorkerThreadResult<L, A> workerResult, final PredicateFactoryRefinement stateFactoryForRefinement)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");

			if (mLogger.isDebugEnabled() && !new Accepts<>(new AutomataLibraryServices(getServices()), minuend,
					(NestedWord<L>) workerResult.getCounterexample().getWord()).getResult()) {
				mLogger.debug("Counterexample of worker result is no longer accepted by the abstraction");
			}

			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			// As in NwaCegarLoop: a proof needs the states that the sigma-star exploitation would skip.
			final boolean exploitSigmaStarConcatOfIa =
					workerResult.getAutomatonType().equals(AutomatonType.FLOYD_HOARE)
							&& (mProofUpdater == null || mProofUpdater.exploitSigmaStarConcatOfIa());
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, subtrahend, psd, exploitSigmaStarConcatOfIa);
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(subtrahend.size());

			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				throw tce;
			} finally {
				// We never enhance in main thread!
			}

			// Future work:
			assert !mPref.dumpOnlyReuseAutomata();
			assert mFaultLocalizationMode == RelevanceAnalysisMode.NONE;

			if (REMOVE_DEAD_ENDS) {
				if (mProofUpdater != null) {
					// SENWA is rejected in the constructor if we compute a proof
					final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
					mProofUpdater.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mProofUpdater != null) {
					mProofUpdater.addDeadEndDoubleDeckers(diff);
				}
			}
			return diff;
		} finally {
		}
	}

	/**
	 * The solver settings of one worker script. Which preference page describes the solver depends on the worker:
	 * <ul>
	 * <li>A TA worker's script plays the part of the main thread's CFG script: weakest preconditions, quantifier
	 * elimination, the predicate unifier and the Hoare triple checks run on it, while its trace checks get their own
	 * solver from the TraceAbstraction page via {@link TaCheckAndRefinementPreferences}. So it reads IcfgBuilder's page,
	 * like the CFG script of the sequential loop. (With the TraceAbstraction page, the SV-COMP bitvector settings ran
	 * all of that on bitwuzla without a per-query timeout, and computing backward predicates took about 20 times as
	 * long as in the sequential loop.)</li>
	 * <li>k-induction and the invariant supplier ask every query on their script, so they read the TraceAbstraction
	 * page: a user who configures a solver for TraceAbstraction expects that solver there. (IcfgBuilder's per-query
	 * timeout used to silently turn the proofs of a long-running k-induction worker into {@code unknown}.)</li>
	 * </ul>
	 *
	 * @param workerType
	 *            the kind of worker this script is for; {@link WorkerType#KINDUCTION} may carry its own per-query
	 *            timeout, see {@link TraceAbstractionPreferenceInitializer#LABEL_KINDUCTION_SOLVER_TIMEOUT}.
	 * @param filename
	 *            base name for a dumped SMT script
	 */
	private SolverSettings getSolverSettings(final WorkerType workerType, final String filename) {

		// The two benchmark-dump flags exist only on IcfgBuilder's page, so every worker reads them there.
		final IPreferenceProvider taPrefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final IPreferenceProvider icfgPrefs = mServices.getPreferenceProvider(
				de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.Activator.PLUGIN_ID);
		final IPreferenceProvider solverPrefs = workerType == WorkerType.TA ? icfgPrefs : taPrefs;

		final SolverMode solverMode;
		final String commandExternalSolver;
		final Logics logicForExternalSolver;
		if (workerType == WorkerType.TA) {
			solverMode = icfgPrefs.getEnum(IcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
			commandExternalSolver = icfgPrefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);
			logicForExternalSolver =
					Logics.valueOf(icfgPrefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		} else {
			solverMode = solverMode(workerType);
			commandExternalSolver = externalSolverCommand(workerType);
			logicForExternalSolver = mPref.logicForExternalSolver();
		}

		final boolean fakeNonIncrementalScript =
				solverPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = mPref.dumpSmtScriptToFile();
		final boolean compressSmtScript = mPref.compressDumpedSmtScript();
		final String pathOfDumpedScript = mPref.pathOfDumpedScript();

		final boolean dumpUnsatCoreTrackBenchmark =
				icfgPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark =
				icfgPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions =
				solverPrefs.getKeyValueMap(IcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						// The worker type in the name: workers started in the same iteration would otherwise dump into
						// the same file and garble each other's script.
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename + workerType,
								compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);

		return solverSettings;
	}

	/**
	 * The solver mode of a worker's solver. k-induction only asks for satisfiability and models, never for an unsat
	 * core, so its solver does not produce them: cvc4 1.8 in incremental mode segfaults on the counterexample
	 * reconstruction's queries when unsat cores are enabled, and without them answers the very same script.
	 */
	private SolverMode solverMode(final WorkerType workerType) {
		final SolverMode configured = mPref.solverMode();
		if (workerType == WorkerType.KINDUCTION && configured == SolverMode.External_ModelsAndUnsatCoreMode) {
			return SolverMode.External_ModelsMode;
		}
		return configured;
	}

	/**
	 * @return the settings of the invariant supplier's probation of k-induction's queries, or {@code null} if it is
	 *         disabled or there is no k-induction worker
	 */
	private InvariantSupplier.Probation probationSettings() {
		if (!mPref.useInvariantProbation() || mNumKInductionWorkers == 0) {
			return null;
		}
		if (System.getProperty("os.name").toLowerCase().startsWith("windows")) {
			mLogger.warn("The probation of invariants needs SIGINT, which Windows does not have; k-induction runs "
					+ "without probation");
			return null;
		}
		// Interrupting a query needs SIGINT, after which z3 answers unknown and keeps its state; the supplier sets
		// z3's :timeout option for its probes.
		final String supplierCommand = externalSolverCommand(WorkerType.INVARIANT);
		if (!isZ3(externalSolverCommand(WorkerType.KINDUCTION)) || !isZ3(supplierCommand)) {
			mLogger.warn("The probation of invariants needs z3 as the solver of k-induction and of the invariant "
					+ "supplier, but the solver command is \"%s\"; k-induction runs without probation",
					mPref.commandExternalSolver());
			return null;
		}
		final Matcher timeout = Pattern.compile("-t:(\\d+)").matcher(supplierCommand);
		final long solverTimeout = timeout.find() ? Long.parseLong(timeout.group(1)) : Z3_NO_TIMEOUT;
		return new InvariantSupplier.Probation(mPref.getProbationFactor(), mPref.getProbationMinimum() * 1000L,
				solverTimeout);
	}

	private static boolean isZ3(final String command) {
		final String executable = command.split("\\s+", 2)[0];
		return "z3".equals(executable.substring(executable.lastIndexOf('/') + 1));
	}

	/**
	 * The external solver command for a worker, with the k-induction per-query timeout applied if one is configured
	 * and this is a k-induction worker.
	 */
	private String externalSolverCommand(final WorkerType workerType) {
		final String command = mPref.commandExternalSolver().trim();
		final int timeout = mPref.getKInductionSolverTimeout();
		if (workerType != WorkerType.KINDUCTION || timeout < 0) {
			// Inherit whatever the configured command says.
			return command;
		}
		final String executable = command.split("\\s+", 2)[0];
		final Entry<Pattern, String> option =
				SOLVER_TIMEOUT_OPTION.get(executable.substring(executable.lastIndexOf('/') + 1));
		if (option == null) {
			throw new UnsupportedOperationException("A k-induction SMT timeout of " + timeout
					+ "ms was configured, but we do not know the per-query timeout option of \"" + executable
					+ "\". Encode the timeout in the solver command instead, or use one of "
					+ SOLVER_TIMEOUT_OPTION.keySet() + ".");
		}
		// Drop any timeout the command already carries, so the k-induction setting wins rather than silently
		// losing to it.
		return option.getKey().matcher(command).replaceAll("").trim() + String.format(option.getValue(), timeout);
	}

	@Override
	protected void finish() {
		// Every way out of the loop shuts the pool down, but a worker may still be busy when we get here.
		mExec.shutdownNow();
		try {
			if (!mExec.awaitTermination(WORKER_TERMINATION_TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
				mLogger.warn("Some workers are still running after %ss", WORKER_TERMINATION_TIMEOUT_SECONDS);
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		}
		detachTransferredEdges();
		super.finish();
	}

	/**
	 * Every letter {@link TransferBetweenMainAndWorker} transfers becomes a new {@code CodeBlock}, and the constructor
	 * of a {@code CodeBlock} connects it to its source and target - which are locations of the main ICFG. So the main
	 * ICFG ends up with a copy of each transferred edge whose transition formula belongs to a worker's script, and
	 * whoever walks the ICFG after the loop (e.g. the check of the Hoare annotation) trips over it. Remove all edges
	 * that were not there before the loop.
	 */
	private void detachTransferredEdges() {
		int removed = 0;
		for (final IcfgLocation loc : mOriginalLocations) {
			final List<IcfgEdge> outgoing = loc.getOutgoingEdges().stream()
					.filter(e -> !mOriginalEdges.contains(e)).collect(Collectors.toList());
			final List<IcfgEdge> incoming = loc.getIncomingEdges().stream()
					.filter(e -> !mOriginalEdges.contains(e)).collect(Collectors.toList());
			loc.removeAllOutgoing(outgoing);
			loc.removeAllIncoming(incoming);
			removed += outgoing.size();
		}
		if (removed > 0) {
			mLogger.info("Detached %s transferred edges from the ICFG", removed);
		}
	}

	private static Set<IcfgLocation> collectLocations(final IIcfg<?> icfg) {
		return icfg.getProgramPoints().values().stream().flatMap(m -> m.values().stream())
				.collect(Collectors.toSet());
	}

	// worker use this method to access the programcache shared across all workers + main
	public PathProgramCache<L> getCurrentProgramCache() {
		return mProgramCache;
	}

}
