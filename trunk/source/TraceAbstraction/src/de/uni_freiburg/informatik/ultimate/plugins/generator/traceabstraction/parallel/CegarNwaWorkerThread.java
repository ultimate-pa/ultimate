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

import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.IInvariantSink;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.InterpolantSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IpTcStrategyModuleAcceleratedTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CegarNwaWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult = null;
	private NestedWordAutomaton<L, IPredicate> mInterpolAutomaton = null;
	private IRun<L, ?> mCounterexample = null;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	// Whether the main thread computes a proof. The worker never builds Hoare states itself, but its difference
	// decides which transitions of the subtrahend get computed, so it must explore what the main thread explores.
	private final boolean mComputeHoareAnnotation;
	private IcfgLocation mCurrentErrorLoc;
	private final SimplificationTechnique mSimplificationTechnique;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	// How often a worker waiting for a task looks whether it was retired
	private static final long RETIREMENT_POLL_MILLIS = 200;
	private final ParallelNwaCegarLoop<L, A> mMainThread;
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	private StrategyFactory<L> mStrategyFactory;
	// communication with controller
	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;

	private final PathProgramCache<L> mProgramCache;
	// the services of the counterexample check that is running, see run()
	private TaskScopedServices mTaskServices;
	// where the interpolants of every infeasible counterexample go, to be checked for invariants
	private final IInvariantSink mInvariantSink;
	// Expires when the HeapWatchdog retires this worker; mServices asks it, so it stops the running check.
	private final RetirementTimer mRetirementTimer;
	// The task whose counterexample is being checked, null while the worker waits for one
	private WorkerThreadTask<L> mTask;

	/**
	 * CegarNwaWorkerThread is a runnable that will be executed by an executor service. It takes counterexamples from
	 * the workerTaskQueue and puts the resulting automata into the blockingQueueForResults. It takes the current
	 * abstraction from the controller, every time it does a difference calculation.
	 *
	 * TransferBetweenMainAndWorker is used to transfer between worker and controller/main cfgScript
	 *
	 * Thread-safety: everything that is given via constructor needs to be thread-save, Most things are freshly created
	 * in when the this object is created. Exceptions are: services, Preferences, the Logger and the PathProgramCache
	 * PathProgramCacheis thread save, the others shouldnt be an issue.
	 *
	 * TODO provide CEGAR loop statistics
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */
	public CegarNwaWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final IInvariantSink invariantSink,
			final RetirementTimer retirementTimer) {

		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mRetirementTimer = retirementTimer;
		mServices = services.getProgressMonitorService().registerChildTimer(services, retirementTimer);
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(mServices);
		mCfgSmtToolkit = cfgSmtToolkit;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
		mProgramCache = new PathProgramCache<>(mLogger);
		mInvariantSink = invariantSink;

		final Thread.UncaughtExceptionHandler exhandler = (th, ex) -> {
			mThreadResult = new WorkerThreadResult<>(WorkerType.TA, null, null, null, mCounterexample, null, true);
			try {
				mBlockingQueueForResults.put(mThreadResult);
				throw new AssertionError("Worker Thread failed due to " + ex);
			} catch (final InterruptedException e) {
				throw new AssertionError("Worker Thread failed due to " + e);
			}
		};
		Thread.currentThread().setUncaughtExceptionHandler(exhandler);

	}

	/*
	 * Gets a counterexamples from the blocking queue, sets up a strategy (checks how often the pathprogram has been
	 * seen). Checks feasibility, interpolates, creates an Error or Interpolant automaton. Calculates the difference to
	 * generalize the interpolant automaton and then puts a @WorkerThreadResult into the blocking queue for results.
	 *
	 * Terminates if the Thread is interrupted (not used atm) or the Executioner service triggers a shutdown. If the
	 * check of a counterexample throws, the worker tells the main thread with a crashed result and takes no more tasks.
	 * If the {@link HeapWatchdog} retires the worker, the check it runs is stopped and the worker tells the main thread
	 * with a retired result, which hands back the counterexample.
	 */
	@Override
	public void run() {
		try {
			while (!Thread.currentThread().isInterrupted()) {
				if (!checkNextCounterexample()) {
					return;
				}
			}
		} finally {
			mRetirementTimer.stopped();
		}
	}

	/**
	 * @return whether the worker takes another task
	 */
	private boolean checkNextCounterexample() {
		// What the task constructs, above all the solvers of its trace checks, is destroyed when it is done.
		mTaskServices = new TaskScopedServices(mServices);
		try {
			mLogger.info("WorkerThread: " + Thread.currentThread() + " is Waiting for a Task");
			mIteration += 1;
			mTask = takeTask();
			if (mTask == null) {
				return retire();
			}
			checkCounterexample(mTask);
			mTask = null;
			return true;
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			return false;
		} catch (final Throwable t) {
			if (mMainThread.isShuttingDown()) {
				// Another worker decided and the main thread destroyed our solver under a running query.
				mLogger.info("WorkerThread: stopping, shut down during a trace check (" + t + ")");
				return false;
			}
			if (mRetirementTimer.isRetired()) {
				// Whatever was thrown, a cancellation or an exception that wraps one, the retirement stopped it.
				return retire();
			}
			mLogger.error("WorkerThread failed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mBlockingQueueForResults.put(WorkerThreadResult.crashed(WorkerType.TA, t));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
			return false;
		} finally {
			mTaskServices.destroyAll(mLogger);
			mTaskServices = null;
		}
	}

	/**
	 * Waits for the next task, but no longer than until the worker is retired.
	 *
	 * @return the task, or null if the worker was retired
	 */
	private WorkerThreadTask<L> takeTask() throws InterruptedException {
		while (!mRetirementTimer.isRetired()) {
			final WorkerThreadTask<L> task = mWorkerTaskQueue.poll(RETIREMENT_POLL_MILLIS, TimeUnit.MILLISECONDS);
			if (task != null) {
				return task;
			}
		}
		return null;
	}

	/**
	 * Tells the main thread that this worker retired, with the counterexample it was checking, if any.
	 *
	 * @return false, the worker takes no more tasks
	 */
	private boolean retire() {
		mLogger.info("WorkerThread: retired, %s", mRetirementTimer.getReason());
		try {
			mBlockingQueueForResults
					.put(WorkerThreadResult.retired(WorkerType.TA, mTask == null ? null : mTask.getCounterexample()));
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		}
		return false;
	}

	/**
	 * Checks the counterexample of one task and puts the result into the queue for the main thread.
	 */
	private void checkCounterexample(final WorkerThreadTask<L> task)
			throws AutomataLibraryException, InterruptedException {
		final IRun<L, ?> mainThreadCounterexample = task.getCounterexample();
		mProgramCache.copyProgramCache(mMainThread.getCurrentProgramCache());
		mCounterexample =
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mainThreadCounterexample, TransferMode.MAIN2WORKER);
		updateAbstractionIfSmaller();

		// set the programCount to x-1, because we will report it again later
		mProgramCache.setPathProgramCount(mCounterexample.getWord(), task.getPathProgramCount() - 1);
		final List<L> trace = mCounterexample.getWord().asList();
		mCurrentErrorLoc = mCounterexample.getSymbol(mCounterexample.getLength() - 2).getTarget();
		final int traceHash = trace.hashCode();
		mLogger.info("Starting Thread: " + Thread.currentThread().threadId() + "# for Trace Check: " + traceHash);
		Thread.currentThread().setName("Worker for " + traceHash);
		final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
		final Counterexample<L> counterexample = new Counterexample<>(mCounterexample.getWord(), locations);
		final ITARefinementStrategy<L> strategy = setUpStrategy(counterexample);
		final Pair<LBool, IProgramExecution<L, Term>> isCexResult = isCounterexampleFeasible(strategy);
		if (isCexResult.getFirst() != LBool.SAT && mRetirementTimer.isRetired()) {
			// An unknown answer may just be the retirement; it must not register a timeout for the error location.
			throw new ToolchainCanceledException(getClass(), "trace check of a retired worker");
		}
		if (isCexResult.getFirst() == LBool.UNSAT) {
			submitInterpolants();
		}

		final AbstractCegarLoop.AutomatonType automatonType = processFeasibilityCheckResult(strategy,
				isCexResult.getFirst(), isCexResult.getSecond(), mCurrentErrorLoc);
		constructRefinementAutomaton(automatonType);
		mThreadResult = refineAbstractionInternally();
		mLogger.info("Done with Thread: " + Thread.currentThread().threadId() + "#");
		mBlockingQueueForResults.put(mThreadResult);
	}

	/**
	 * Hands every interpolant sequence of the infeasibility proof to the invariant supplier, which keeps what is
	 * inductive. The interpolants are terms of this worker's script; the supplier copies them on its own thread.
	 */
	private void submitInterpolants() {
		final List<QualifiedTracePredicates> sequences = mRefinementResult.getUsedTracePredicates();
		if (sequences == null) {
			return;
		}
		final List<IcfgLocation> locations = getIcfgLocationsFromRun(mCounterexample);
		// The interpolants are those between two letters, i.e. at the states 1..n-1 of the run.
		final List<IcfgLocation> inner = locations.subList(1, locations.size() - 1);
		for (final QualifiedTracePredicates sequence : sequences) {
			final List<Term> interpolants =
					sequence.getPredicates().stream().map(IPredicate::getFormula).collect(Collectors.toList());
			mInvariantSink.submit(new InterpolantSequence(mCfgSmtToolkit.getManagedScript(), inner, interpolants,
					"TA " + sequence.getOrigin().getSimpleName()));
		}
	}

	protected List<?> getControlConfigurationsFromCounterexample(final IRun<L, ?> run) {
		return getIcfgLocationsFromRun(run);
	}

	private List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	/*
	 * The worker creates for each counterexample a new strategy module. We can switch between different
	 * RefinementStrateies here. For example we can use {@link RefinementStrategy.ACCELERATED_TRACE_CHECK} if we have
	 * seen the pp 7 times.
	 *
	 * if (mStrategyFactory.getPathProgramCache().getPathProgramCount(mCounterexample.getWord()) == 7 ) { strategy =
	 * mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction, new
	 * SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration), mPredicateFactoryInterpolantAutomata,
	 * getPreconditionProvider(), getPostconditionProvider(), RefinementStrategy.ACCELERATED_TRACE_CHECK); }
	 *
	 * Warning, we have shared (read and write) access to the PathProgramCache here. But the PathProgramCache uses
	 * thread save lists and maps.
	 */
	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) {
		mStrategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs, mCfgSmtToolkit,
				mPredicateFactory, mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz, mProgramCache);

		final ITARefinementStrategy<L> strategy;
		strategy = mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
				new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				mPref.getRefinementStrategy());
		return strategy;
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, TransferMode.MAIN2WORKER);
		return workerAbstraction;
	}

	private void updateAbstractionIfSmaller() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		if (mainAbstraction instanceof NestedWordAutomaton && mainAbstraction.size() < mAbstraction.size()) {
			mLogger.info("Updating worker A, since main A " + mainAbstraction.size() + " is smaller than worker A "
					+ mAbstraction.size());
			mAbstraction = (INestedWordAutomaton<L, IPredicate>) mNwaCexTransferrer.transferAutomaton(mainAbstraction,
					mPredicateFactoryInterpolantAutomata, TransferMode.MAIN2WORKER);
		}

	}

	private IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	private IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	protected Pair<LBool, IProgramExecution<L, Term>>
			isCounterexampleFeasible(final ITARefinementStrategy<L> strategy) {
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample.getWord())) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();

		} catch (final ToolchainCanceledException | SMTLIBException tce) {
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
			((IcfgProgramExecution<L>) rcfgProgramExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());
		}
		// TODO use some kind of mCegarLoopBenchmark (currently leads to concurrency problems)
		return new Pair<>(feasibility, rcfgProgramExecution);
	}

	/**
	 * Report results from a feasibility check if necessary and return the type of the refinement automaton
	 *
	 * @param strategy
	 */
	private AbstractCegarLoop.AutomatonType processFeasibilityCheckResult(final ITARefinementStrategy<L> strategy,
			final LBool isCounterexampleFeasible, final IProgramExecution<L, Term> programExecution,
			final IcfgLocation currentErrorLoc) {
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
			for (final ITraceCheckStrategyModule<L, ?> module : strategy.getTraceCheckModules()) {
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

	/**
	 * This Method does not do the sanity checks done in NWA for the correctness of Error and Interpolant automata!
	 *
	 * @param automatonType
	 * @throws AutomataOperationCanceledException
	 */
	private void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType)
			throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
					mRefinementResult.getPredicateUnifier(), mCfgSmtToolkit, mSimplificationTechnique,
					mCfgSmtToolkit.getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction, mIteration);
			mInterpolAutomaton = null;
			break;
		case INTERPOLANT:
			mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();
			break;
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected IUltimateServiceProvider getServices() {
		return mTaskServices != null ? mTaskServices : mServices;
	}

	private WorkerThreadResult<L, A> refineAbstractionInternally() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = AutomatonType.ERROR;
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		} else {
			automatonType = AutomatonType.FLOYD_HOARE;
			useErrorAutomaton = false;
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(enhanceMode, predicateUnifier, htc, subtrahendBeforeEnhancement);

		}

		mLogger.info("Difference in Worker for Generalization");
		computeAutomataDifference(mAbstraction, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(WorkerType.TA,
				mNwaCexTransferrer.transferAutomaton(subtrahend, mPredicateFactoryInterpolantAutomata,
						TransferMode.WORKER2MAIN),
				automatonType, mCfgSmtToolkit.getManagedScript(),
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mCounterexample, TransferMode.WORKER2MAIN),
				mPredicateFactory, false);

		// TODO missing a lot of stuff from NwaCegarLoop

		return workerResult;
	}

	/*
	 * WARNING The real difference has to be computed in the Main Thrad / CEGAR loop This is only used to enhance the
	 * interpolant automaton
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			return null;
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

			if (REMOVE_DEAD_ENDS) {
				diff.removeDeadEnds();
			}
			return diff;
		} finally {
			mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());
			mLogger.info(htc.getStatistics());
			mLogger.info(htc);
			mLogger.debug("WORKER: Finished constructing difference");
		}

	}

	private RunningTaskInfo executeDifferenceTimeoutActions(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) throws AutomataLibraryException {
		final RunningTaskInfo runningTaskInfo =
				getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement, automatonType);
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
		final HoareTripleCheckerCache initialCache =
				TraceAbstractionUtils.extractHoareTriplesfromAutomaton(mRefinementResult.getInfeasibilityProof());
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
				mPref.getHoareTripleChecks(), mCfgSmtToolkit, mRefinementResult.getPredicateUnifier(), initialCache);
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
		return new NondeterministicInterpolantAutomaton<>(getServices(), mCfgSmtToolkit, htc, inputInterpolantAutomaton,
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
		return new DeterministicInterpolantAutomaton<>(getServices(), mCfgSmtToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
	}
}
