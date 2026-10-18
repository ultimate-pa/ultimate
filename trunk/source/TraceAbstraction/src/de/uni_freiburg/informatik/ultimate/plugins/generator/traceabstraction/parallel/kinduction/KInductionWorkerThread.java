/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.kinduction;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.BlockingQueue;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.HeapBudgetTimer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadTask;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionCounterexampleException;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;

/**
 * Worker thread running {@link KInduction} inside {@link ParallelNwaCegarLoop}'s thread pool. It runs once (see
 * {@link #run()}) on the whole program and reports a {@link WorkerThreadResult} sentinel when the program is safe.
 * <p>
 * When k-induction refutes the program, {@link KInduction} reconstructs a concrete run from the solver's model and
 * this class reports it the same way {@code CegarNwaWorkerThread} reports a feasible counterexample: it runs the
 * counterexample through the refinement engine to obtain an {@code IcfgProgramExecution} with values, registers
 * {@code Result.UNSAFE} on the shared result builder, and hands the main thread a result marked
 * {@link AutomatonType#ERROR} so that it terminates instead of refining. It carries no error-automaton scaffolding:
 * the whole program is refuted at once, so there is nothing left to refine.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class KInductionWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final boolean mComputeHoareAnnotation;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	public final ParallelNwaCegarLoop<L, A> mMainThread;
	private final INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	private final TaskIdentifier mTaskIdentifier;
	private final IInvariantSupplier<CallNode<IPredicate>> mInvariantSupplier;
	// Only used to build a refinement strategy for a counterexample; k-induction has no path-program history.
	private final PathProgramCache<L> mProgramCache;
	// Stops k-induction when the live heap exceeds its memory budget. Everything k-induction runs gets
	// mKInductionServices, whose progress monitor asks this timer, so every poll of continueProcessing() checks it.
	private final HeapBudgetTimer mHeapTimer;
	private final IUltimateServiceProvider mKInductionServices;
	// The invariants of a proof for the main thread's correctness witness, see computeWitnessInvariants
	private Map<IPredicate, Term> mWitnessInvariants;
	// How long computing them may delay the verdict
	private static final long WITNESS_TIMEOUT_MILLIS = 10_000;

	public KInductionWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final TaskIdentifier taskIdentifier,
			final IInvariantSupplier<CallNode<IPredicate>> invariantSupplier) throws InterruptedException {
		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mCfgSmtToolkit = cfgSmtToolkit;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAndTransferAbstraction();
		mTaskIdentifier = taskIdentifier;
		mInvariantSupplier = invariantSupplier;
		mProgramCache = new PathProgramCache<>(mLogger);
		final IProgressMonitorService progressMonitor = services.getProgressMonitorService();
		mHeapTimer = new HeapBudgetTimer(progressMonitor,
				Runtime.getRuntime().maxMemory() / 100 * pref.getKInductionMemoryBudget(), true);
		mKInductionServices = progressMonitor.registerChildTimer(services, mHeapTimer);
	}

	@Override
	public void run() {
		Thread.currentThread().setName("KInduction Thread");
		try {
			mLogger.info("WorkerThread for KInduction Starts");
			mIteration = 1;
			switch (runKInduction()) {
			case SAFE:
				mBlockingQueueForResults.put(WorkerThreadResult.kInductionSafe(mWitnessInvariants,
						mCfgSmtToolkit.getManagedScript()));
				break;
			case UNSAFE:
				// The violation is already registered on the shared result builder. AutomatonType.ERROR is what
				// tells the main thread that this is a refutation and not the "safe" sentinel, which carries a
				// null automaton type; no subtrahend, because there is nothing left to refine.
				mBlockingQueueForResults.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null,
						AutomatonType.ERROR, null, null, null, false));
				break;
			case NO_VERDICT:
				mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
				break;
			case RETIRED:
				// retireForMemory already told the main thread
				break;
			default:
				throw new AssertionError("unknown k-induction verdict");
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final Throwable t) {
			if (mMainThread.isShuttingDown()) {
				// Another worker decided and the main thread destroyed our solver under a running query.
				mLogger.info("KInduction worker: stopping, shut down during a query (" + t + ")");
				return;
			}
			if (mHeapTimer.isHeapBudgetExceeded()) {
				// Whatever was thrown, a cancellation or an exception that wraps one, it is the memory budget.
				retireForMemory(t);
				return;
			}
			mLogger.error("KInduction worker crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mBlockingQueueForResults
						.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null, null, null, null, null, true));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		} finally {
			if (mHeapTimer.getCollections() > 0) {
				mLogger.info("KInduction: its memory budget collected garbage %d time(s) to check the live heap and "
						+ "trim the committed one", mHeapTimer.getCollections());
			}
		}
	}

	private enum Verdict {
		SAFE, UNSAFE, NO_VERDICT, RETIRED
	}

	/**
	 * Logs that k-induction ran out of its memory budget and retires the worker without a verdict.
	 *
	 * @param stop
	 *            what k-induction threw when the budget stopped it, or null if it ended on its own
	 */
	private void retireForMemory(final Throwable stop) {
		final long maxHeap = Runtime.getRuntime().maxMemory();
		mLogger.warn(
				"KInduction: stopped, it exceeded its memory budget: %d MB of heap still live after a garbage "
						+ "collection, budget %d MB (%d%% of the %d MB max heap), while %s. The k-induction worker "
						+ "retires without a verdict.",
				mHeapTimer.getHeapUsedWhenExceeded() >> 20, mHeapTimer.getBudgetBytes() >> 20,
				mPref.getKInductionMemoryBudget(), maxHeap >> 20, describe(stop));
		try {
			mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		}
		// Most of the heap was ours. Collecting it now lets the JVM shrink its heap instead of keeping it committed
		// while the other workers and their solvers need the memory.
		System.gc();
	}

	/**
	 * @return what k-induction was doing when it was stopped, from the running tasks of a cancellation
	 */
	private static String describe(final Throwable stop) {
		if (stop == null) {
			return "a solver query, which then answered unknown";
		}
		for (Throwable cause = stop; cause != null; cause = cause.getCause()) {
			if (cause instanceof IRunningTaskStackProvider) {
				final String tasks = ((IRunningTaskStackProvider) cause).getRunningTaskStack().stream()
						.map(RunningTaskInfo::getTaskDescription).filter(Objects::nonNull)
						.collect(Collectors.joining(", "));
				if (!tasks.isEmpty()) {
					return tasks;
				}
			}
		}
		return stop.getMessage() != null ? stop.getMessage() : stop.getClass().getSimpleName();
	}

	private Verdict runKInduction() throws AutomataLibraryException, InterruptedException {
		final KInduction<L, IPredicate> kInduction = new KInduction<>(mKInductionServices, mLogger, mCfgSmtToolkit,
				mAbstraction, mInvariantSupplier, mPref.restartKInductionSolverAfterInterrupt());
		if (kInduction.wasUnkown() && mHeapTimer.isHeapBudgetExceeded()) {
			// The budget stopped a query, which answered unknown instead of throwing.
			retireForMemory(null);
			return Verdict.RETIRED;
		}
		if (kInduction.wasUnkown()) {
			// Not a crash: the encoding is fine, the query was just not decided. Retiring this worker leaves the
			// other workers - and, if there are none, the main thread's UNKNOWN result - to speak for the program.
			// The unrolling bound and a solver that gave up are entirely different situations, so name which one.
			mLogger.warn("KInduction: " + kInduction.getInconclusive());
			return Verdict.NO_VERDICT;
		}
		if (kInduction.isSafe()) {
			if (mComputeHoareAnnotation) {
				mWitnessInvariants = computeWitnessInvariants(kInduction);
			}
			return Verdict.SAFE;
		}
		// No transfer: the run is built over the worker's own abstraction with worker-script letters, and the
		// refinement engine below runs on the worker toolkit, exactly as in CegarNwaWorkerThread.
		reportCounterexample(kInduction.getCounterexample());
		return Verdict.UNSAFE;
	}

	/**
	 * The invariants of the proof for a correctness witness, by loop head. A loop head is a state of
	 * {@link #mAbstraction}, which shares its states with the main thread's initial abstraction, see
	 * {@link TransferBetweenMainAndWorker#transferAutomaton}.
	 *
	 * @return the invariants, worker-script terms, or null if there are none; never throws, since the proof stands
	 *         without a witness
	 */
	private Map<IPredicate, Term> computeWitnessInvariants(final KInduction<L, IPredicate> kInduction) {
		// The verdict waits for this, so a slow quantifier elimination must not hold it back for long.
		final IProgressMonitorService progressMonitor = mKInductionServices.getProgressMonitorService();
		final IUltimateServiceProvider witnessServices = progressMonitor.registerChildTimer(mKInductionServices,
				progressMonitor.getChildTimer(WITNESS_TIMEOUT_MILLIS));
		try {
			final Optional<Map<CallNode<IPredicate>, Term>> invariants =
					kInduction.computeWitnessInvariants(witnessServices, mPref.getSimplificationTechnique());
			if (invariants.isEmpty()) {
				return null;
			}
			final Map<IPredicate, Term> result = new LinkedHashMap<>();
			for (final Map.Entry<CallNode<IPredicate>, Term> entry : invariants.get().entrySet()) {
				final IPredicate state = entry.getKey().getState();
				final IcfgLocation loc = ((ISLPredicate) state).getProgramPoint();
				// A callee unfolded at several call sites has a loop head per call site, but a location only one
				// invariant.
				if (result.put(state, entry.getValue()) != null) {
					mLogger.warn("KInduction: no correctness witness invariants, %s is a loop head at several call "
							+ "sites", loc);
					return null;
				}
				final IProgramVar outOfScope = findOutOfScopeVariable(entry.getValue(), loc.getProcedure());
				if (outOfScope != null) {
					mLogger.warn("KInduction: no correctness witness invariants, the invariant of %s mentions %s, "
							+ "which is not in scope there", loc, outOfScope);
					return null;
				}
			}
			return result;
		} catch (final ToolchainCanceledException | SMTLIBException e) {
			mLogger.warn("KInduction: no correctness witness invariants, computing them failed: " + e);
			return null;
		} catch (final RuntimeException | AssertionError e) {
			// A bug in the witness computation must not cost the verdict, but it should be visible.
			mLogger.error("KInduction: no correctness witness invariants, computing them crashed: " + e);
			for (final StackTraceElement element : e.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			return null;
		}
	}

	/**
	 * @return a variable of {@code invariant} that is neither global nor a local of {@code procedure}, or null. The
	 *         transition system is flat, so the invariant of a loop head in a callee may speak about its callers.
	 */
	private IProgramVar findOutOfScopeVariable(final Term invariant, final String procedure) {
		for (final TermVariable tv : invariant.getFreeVars()) {
			final IProgramVar pv = mCfgSmtToolkit.getSymbolTable().getProgramVar(tv);
			if (pv == null || !pv.isGlobal() && !procedure.equals(pv.getProcedure())) {
				return pv;
			}
		}
		return null;
	}

	/**
	 * Registers a k-induction counterexample as {@code Result.UNSAFE}, going through the same refinement engine
	 * {@code CegarNwaWorkerThread} uses, so that the reported program execution carries variable values and
	 * backtranslates to the input program like any other counterexample.
	 */
	private void reportCounterexample(final NestedRun<L, IPredicate> counterexample) {
		final List<IcfgLocation> locations = new ArrayList<>();
		for (final IPredicate state : counterexample.getStateSequence()) {
			if (!(state instanceof ISLPredicate)) {
				throw new KInductionCounterexampleException("abstraction state " + state + " is a "
						+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no program point");
			}
			locations.add(((ISLPredicate) state).getProgramPoint());
		}
		final Counterexample<L> cex = new Counterexample<>(counterexample.getWord(), locations);

		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mPredicateFactory, mPredicateFactoryInterpolantAutomata,
				mMainThread.mTransitionClazz, mProgramCache);
		final ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(mKInductionServices, cex,
				mAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, mIteration),
				mPredicateFactoryInterpolantAutomata,
				IPreconditionProvider.constructDefaultPreconditionProvider(),
				IPostconditionProvider.constructDefaultPostconditionProvider(), mPref.getRefinementStrategy());
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
				new TraceAbstractionRefinementEngine<>(mKInductionServices, mLogger, strategy).getResult();

		final LBool feasibility = refinementResult.getCounterexampleFeasibility();
		if (feasibility != LBool.SAT) {
			// Not an unsupported case: k-induction and the letter-level semantics of the very same abstraction
			// cannot both be right here, so one of the two encodings is wrong.
			throw new AssertionError("k-induction refuted the program, but the trace check of the reconstructed "
					+ "run answered " + feasibility + " instead of sat. The k-induction encoding and the "
					+ "letter-level semantics of the abstraction disagree. Run: " + counterexample.getWord());
		}

		final IProgramExecution<L, Term> programExecution;
		if (refinementResult.providesIcfgProgramExecution()) {
			programExecution = refinementResult.getIcfgProgramExecution();
		} else {
			programExecution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(counterexample.getWord());
		}
		((IcfgProgramExecution<L>) programExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());

		mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
		if (mPref.stopAfterFirstViolation()) {
			mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
		}
		mLogger.info("KInduction: reported a counterexample of %d letter(s) as UNSAFE",
				counterexample.getWord().length());
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only), then transfers it to the worker script.
	 */
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAndTransferAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		return mNwaCexTransferrer.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata,
				TransferMode.MAIN2WORKER);
	}
}
