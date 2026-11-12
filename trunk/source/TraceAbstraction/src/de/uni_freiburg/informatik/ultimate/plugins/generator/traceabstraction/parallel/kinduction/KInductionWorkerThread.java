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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.lib.icfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.lib.icfg.util.IcfgEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadTask;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction.WitnessInvariants;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionCounterexampleException;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionWaypoints;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionWaypoints.Level;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Worker thread running {@link KInduction} inside {@link ParallelNwaCegarLoop}'s thread pool. It runs once (see
 * {@link #run()}) on the whole program and reports a {@link WorkerThreadResult} sentinel when the program is safe.
 * <p>
 * When k-induction refutes the program, this class reports the letters a witness can name from the solver's model (see
 * {@link #reportWaypoints}), registers {@code Result.UNSAFE} on the shared result builder, and hands the main thread a
 * result marked {@link AutomatonType#ERROR} so that it terminates instead of refining. It carries no error-automaton
 * scaffolding: the whole program is refuted at once, so there is nothing left to refine.
 * <p>
 * The static methods are shared with {@code NwaCegarLoopWithKInduction}, which runs k-induction on the main thread.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class KInductionWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final boolean mComputeHoareAnnotation;
	public final ParallelNwaCegarLoop<L, A> mMainThread;
	private final INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	private final IInvariantSupplier<CallNode<IPredicate>> mInvariantSupplier;
	// k-induction has no memory limit: when the heap fills up, the other workers retire (see HeapWatchdog).
	private final IUltimateServiceProvider mKInductionServices;
	// The invariants of a proof for the main thread's correctness witness, see computeWitnessInvariants
	private WitnessInvariants<IPredicate> mWitnessInvariants;
	// How much longer than its timer (TAPreferences.getKInductionWitnessTimeout) the verdict waits for a computation
	// that has not noticed the timer yet
	private static final long WITNESS_GRACE_MILLIS = 500;

	public KInductionWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils,
			final IInvariantSupplier<CallNode<IPredicate>> invariantSupplier) throws InterruptedException {
		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAndTransferAbstraction();
		mInvariantSupplier = invariantSupplier;
		mKInductionServices = services;
	}

	@Override
	public void run() {
		Thread.currentThread().setName("KInduction Thread");
		try {
			mLogger.info("WorkerThread for KInduction Starts");
			mIteration = 1;
			switch (runKInduction()) {
			case SAFE:
				mBlockingQueueForResults.put(WorkerThreadResult.kInductionSafe(
						mWitnessInvariants == null ? null : mWitnessInvariants.invariants(),
						mWitnessInvariants != null && mWitnessInvariants.proving(), mCfgSmtToolkit.getManagedScript()));
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
			if (isLimit(t)) {
				// Not a bug in k-induction: its solver gave up or it could not build a run. The other workers go on.
				mLogger.warn("KInduction: stopped by %s; the k-induction worker retires without a verdict", t);
				if (mLogger.isDebugEnabled()) {
					for (final StackTraceElement element : t.getStackTrace()) {
						mLogger.debug("\tat " + element);
					}
				}
				try {
					mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
				} catch (final InterruptedException e) {
					Thread.currentThread().interrupt();
				}
				return;
			}
			mLogger.error("KInduction worker crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mBlockingQueueForResults.put(WorkerThreadResult.crashed(WorkerType.KINDUCTION, t));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	/**
	 * @return whether k-induction stopped at a limit rather than at a bug: its solver failed (out of memory,
	 *         crashed, or rejected the query), it could not express a violation as a run, or the program uses something
	 *         k-induction does not support. A crash still only retires the worker; this decides how it is logged.
	 */
	public static boolean isLimit(final Throwable t) {
		if (t instanceof UnsupportedOperationException) {
			return true;
		}
		for (Throwable cause = t; cause != null; cause = cause.getCause()) {
			if (cause instanceof SMTLIBException || cause instanceof KInductionCounterexampleException) {
				return true;
			}
		}
		return false;
	}

	private enum Verdict {
		SAFE, UNSAFE, NO_VERDICT
	}

	private Verdict runKInduction() throws AutomataLibraryException, InterruptedException {
		final boolean overapproximated = hasOverapproximation(mAbstraction, mLogger);
		final KInduction<L, IPredicate> kInduction = new KInduction<>(mKInductionServices, mLogger, mCfgSmtToolkit,
				mAbstraction, mInvariantSupplier, mPref.restartKInductionSolverAfterInterrupt());
		if (kInduction.wasUnkown()) {
			// Not a crash: the encoding is fine, the query was just not decided. Retiring this worker leaves the
			// other workers - and, if there are none, the main thread's UNKNOWN result - to speak for the program.
			mLogger.warn("KInduction: " + kInduction.getInconclusive());
			return Verdict.NO_VERDICT;
		}
		if (kInduction.isSafe()) {
			if (mComputeHoareAnnotation) {
				mWitnessInvariants = computeWitnessInvariants(kInduction, mKInductionServices, mPref, mCfgSmtToolkit,
						mMainThread::isShuttingDown, mLogger);
			}
			return Verdict.SAFE;
		}
		if (overapproximated) {
			mLogger.warn("KInduction: found a violation, but the program is overapproximated, so it may be spurious; "
					+ "the k-induction worker retires without a verdict");
			return Verdict.NO_VERDICT;
		}
		reportWaypoints(kInduction.getWaypoints(), mResultBuilder, mKInductionServices,
				mCfgSmtToolkit.getManagedScript(), mPref.stopAfterFirstViolation(), mLogger);
		return Verdict.UNSAFE;
	}

	/**
	 * Whether a letter of {@code abstraction} overapproximates the program, e.g. a bitwise operator or a float
	 * comparison in the integer translation, or a math function. A model of the base case can then be spurious, and
	 * the waypoint letters, only a subsequence of the run, miss the Overapprox annotations by which the reporter would
	 * turn UNSAFE into "unable to determine feasibility" (11-10 run: 1,377 of the 1,383 wrong FALSE, nearly all in the
	 * integer run). So a violation of such a program is no verdict.
	 */
	public static <L extends IIcfgTransition<?>> boolean hasOverapproximation(
			final INestedWordAutomaton<L, IPredicate> abstraction, final ILogger logger) {
		final HashRelation<String, ILocation> overapproximations = overapproximations(abstraction);
		if (overapproximations.isEmpty()) {
			return false;
		}
		logger.info("KInduction: the program has %d overapproximation(s), e.g. %s, so a violation is no verdict",
				overapproximations.size(),
				overapproximations.getDomain().iterator().next());
		return true;
	}

	/**
	 * @return what the letters of {@code abstraction} overapproximate, see {@link #hasOverapproximation}, by the name of
	 *         the operation
	 */
	public static <L extends IIcfgTransition<?>> HashRelation<String, ILocation>
			overapproximations(final INestedWordAutomaton<L, IPredicate> abstraction) {
		final List<L> letters = new ArrayList<>(abstraction.getVpAlphabet().getInternalAlphabet());
		letters.addAll(abstraction.getVpAlphabet().getCallAlphabet());
		letters.addAll(abstraction.getVpAlphabet().getReturnAlphabet());
		return Overapprox.getOverapproximations(letters);
	}

	/**
	 * The invariants of the proof for a correctness witness, by loop head. A loop head is a state of the abstraction
	 * k-induction ran on, which shares its states with the abstraction of the main thread it was transferred from, see
	 * {@link TransferBetweenMainAndWorker#transferAutomaton}.
	 *
	 * @param services
	 *            the services k-induction ran with
	 * @param toolkit
	 *            the toolkit of k-induction's script
	 * @param shuttingDown
	 *            whether the CEGAR loop is done, which is why the computation may fail
	 * @return the invariants, terms of k-induction's script, or null if there are none; throws only when interrupted,
	 *         since the proof stands without a witness
	 */
	public static <L extends IIcfgTransition<?>> WitnessInvariants<IPredicate> computeWitnessInvariants(
			final KInduction<L, IPredicate> kInduction, final IUltimateServiceProvider services,
			final TAPreferences pref, final CfgSmtToolkit toolkit, final BooleanSupplier shuttingDown,
			final ILogger logger) throws InterruptedException {
		final long timeout = pref.getKInductionWitnessTimeout();
		// Set when the verdict went without the computation, which may still be running
		final AtomicBoolean abandoned = new AtomicBoolean();
		// The timer of computeWitnessInvariantsWithin only ends the computation where it looks at it, and the ite
		// removal of the quantifier elimination does not: it ran for minutes and the verdict never came. So the verdict
		// waits for the computation only until the timer has run out, and an unfinished one is left behind with the
		// best invariants it has proven so far. It only uses k-induction's own script, which nobody needs once there
		// is a verdict.
		final FutureTask<WitnessInvariants<IPredicate>> task = new FutureTask<>(() -> computeWitnessInvariantsWithin(
				kInduction, services, pref, toolkit, timeout, () -> abandoned.get() || shuttingDown.getAsBoolean(),
				abandoned, logger));
		final Thread thread = new Thread(task, "KInduction witness");
		thread.setDaemon(true);
		thread.start();
		WitnessInvariants<IPredicate> invariants;
		try {
			invariants = task.get(timeout + WITNESS_GRACE_MILLIS, TimeUnit.MILLISECONDS);
		} catch (final TimeoutException e) {
			abandoned.set(true);
			thread.interrupt();
			invariants = kInduction.getBestWitnessInvariants();
			logger.warn("KInduction: computing the correctness witness invariants did not end within %d ms, %s",
					timeout + WITNESS_GRACE_MILLIS,
					invariants == null ? "there are none" : "using the best ones found so far");
		} catch (final ExecutionException e) {
			// computeWitnessInvariantsWithin catches everything but errors such as running out of memory
			logger.error("KInduction: computing the correctness witness invariants failed: " + e.getCause());
			invariants = kInduction.getBestWitnessInvariants();
		}
		if (invariants == null) {
			logger.warn("KInduction: no correctness witness invariants for the proof at k=%d", kInduction.getProvedK());
			return null;
		}
		return invariants;
	}

	/**
	 * @param quiet
	 *            whether a failure is expected: the verdict went without the computation, or the CEGAR loop is done
	 * @return the invariants of {@link KInduction#computeWitnessInvariants}, or the best ones it found before it failed,
	 *         or null if there are none
	 */
	private static <L extends IIcfgTransition<?>> WitnessInvariants<IPredicate> computeWitnessInvariantsWithin(
			final KInduction<L, IPredicate> kInduction, final IUltimateServiceProvider services,
			final TAPreferences pref, final CfgSmtToolkit toolkit, final long timeout, final BooleanSupplier quiet,
			final AtomicBoolean abandoned, final ILogger logger) {
		final IProgressMonitorService progressMonitor = services.getProgressMonitorService();
		final IUltimateServiceProvider witnessServices =
				progressMonitor.registerChildTimer(services, progressMonitor.getChildTimer(timeout));
		try {
			return kInduction
					.computeWitnessInvariants(witnessServices, pref.getSimplificationTechnique(),
							(state, tv) -> isInScope(toolkit, tv,
									((ISLPredicate) state).getProgramPoint().getProcedure()))
					.orElse(null);
		} catch (final ToolchainCanceledException | SMTLIBException e) {
			if (!abandoned.get()) {
				logger.warn("KInduction: computing the correctness witness invariants stopped: " + e);
			}
			return kInduction.getBestWitnessInvariants();
		} catch (final RuntimeException | AssertionError e) {
			if (quiet.getAsBoolean()) {
				// Left behind, the CEGAR loop may have destroyed the solver under it.
				return null;
			}
			// A bug in the witness computation must not cost the verdict, but it should be visible. What was proven
			// before it is still proven.
			logger.error("KInduction: computing the correctness witness invariants crashed: " + e);
			for (final StackTraceElement element : e.getStackTrace()) {
				logger.error("\tat " + element);
			}
			return kInduction.getBestWitnessInvariants();
		}
	}

	/**
	 * @return whether {@code tv} is a global variable or a local of {@code procedure}. The transition system is flat, so
	 *         the invariant of a loop head in a callee may speak about its callers. A variable the symbol table does not
	 *         know, such as the stack pointer of {@code CallStack}, does not exist in the program at all, so it is out
	 *         of scope too.
	 */
	private static boolean isInScope(final CfgSmtToolkit toolkit, final TermVariable tv, final String procedure) {
		final IProgramVar pv = toolkit.getSymbolTable().getProgramVar(tv);
		return pv != null && (pv.isGlobal() || procedure.equals(pv.getProcedure()));
	}

	/**
	 * Registers a violation as {@code Result.UNSAFE} that is known only by the letters a witness can name, see
	 * {@link KInductionWaypoints}. They are a subsequence of the letters of the violation, as a program execution
	 * without values. Nothing here confirms the violation, the model of k-induction is the only evidence.
	 * <p>
	 * The model proves the violation by itself, so the verdict never depends on the witness: if the letters cannot be
	 * backtranslated, only the target is reported, and if that fails too, or the target is not known, an empty execution
	 * at the error location. Each step down is logged with its reason.
	 *
	 * @param services
	 *            the services k-induction ran with, for the trial backtranslation
	 * @param script
	 *            the script of the letters' transition formulas
	 */
	public static <L extends IIcfgTransition<?>> void reportWaypoints(final KInductionWaypoints<L, IPredicate> waypoints,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final ManagedScript script, final boolean stopAfterFirstViolation, final ILogger logger) {
		final List<L> allLetters = waypoints.getLetters();
		final L target = waypoints.getTargetLetter();
		IcfgProgramExecution<L> programExecution = null;
		Level level = waypoints.getLevel();
		if (level == Level.FULL) {
			try {
				programExecution =
						backtranslatableExecution(withoutInlinedCallBoundaries(allLetters), services, script);
			} catch (final ToolchainCanceledException e) {
				throw e;
			} catch (final RuntimeException e) {
				logger.warn("KInduction: the waypoint letters cannot be reported (%s), reporting only the target", e);
				level = Level.TARGET_ONLY;
			}
		}
		if (level == Level.TARGET_ONLY) {
			try {
				programExecution =
						backtranslatableExecution(withoutInlinedCallBoundaries(List.of(target)), services, script);
			} catch (final ToolchainCanceledException e) {
				throw e;
			} catch (final RuntimeException e) {
				logger.warn("KInduction: the target %s cannot be reported (%s), reporting the violation without a "
						+ "waypoint", target, e);
				level = Level.EMPTY;
			}
		}
		if (level == Level.EMPTY) {
			final IcfgLocation errorLocation = programPoint(waypoints.getErrorState());
			resultBuilder.addResult(errorLocation, Result.UNSAFE, emptyExecution(), null, null);
		} else {
			resultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
		}
		if (stopAfterFirstViolation) {
			resultBuilder.addResultForAllRemaining(Result.UNKNOWN);
		}
		logger.info("KInduction: reported a violation with %d waypoint letter(s) of %d (witness level %s), no run was "
				+ "built", programExecution == null ? 0 : programExecution.getLength(), allLetters.size(), level);
	}

	/**
	 * @return the letters as a program execution without values, which the backtranslation has been tried on: the main
	 *         thread backtranslates it again for the result and the witness, and a failure there would cost the verdict
	 */
	@SuppressWarnings("unchecked")
	private static <L extends IIcfgTransition<?>> IcfgProgramExecution<L> backtranslatableExecution(
			final List<L> letters, final IUltimateServiceProvider services, final ManagedScript script) {
		final IcfgProgramExecution<L> programExecution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(
				new Word<>((L[]) letters.toArray(new IIcfgTransition<?>[letters.size()])));
		programExecution.setOriginCfgScript(script);
		services.getBacktranslationService().translateProgramExecution(programExecution);
		return programExecution;
	}

	/** An execution of no letters, as Sifa reports one: the backtranslation accepts only an IcfgProgramExecution. */
	@SuppressWarnings("unchecked")
	private static <L extends IIcfgTransition<?>> IProgramExecution<L, Term> emptyExecution() {
		return (IProgramExecution<L, Term>) (IProgramExecution<?, Term>) IcfgProgramExecution.create(IcfgEdge.class);
	}

	private static IcfgLocation programPoint(final IPredicate state) {
		if (!(state instanceof ISLPredicate)) {
			throw new KInductionCounterexampleException("abstraction state " + state + " is a "
					+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no program point");
		}
		return ((ISLPredicate) state).getProgramPoint();
	}

	/**
	 * The backtranslation of the procedure inliner matches the start of an inlined call with its end, so it does not
	 * accept one without the other, which the waypoint letters could have as they leave out arbitrary letters. Hence no
	 * letter at the location of a letter with such a boundary is kept. As for all waypoints, it is every visit of a
	 * location or none.
	 *
	 * @param letters
	 *            the waypoint letters; the last one leads to the error
	 * @throws KInductionCounterexampleException
	 *             if the letter that leads to the error has such a boundary, since it cannot be left out
	 */
	private static <L extends IIcfgTransition<?>> List<L> withoutInlinedCallBoundaries(final List<L> letters) {
		final InlinedCallBoundaryFinder finder = new InlinedCallBoundaryFinder();
		final L target = letters.get(letters.size() - 1);
		if (finder.hasBoundary(target)) {
			throw new KInductionCounterexampleException("k-induction refuted the program, but the letter that leads to "
					+ "the error starts or ends an inlined call, so it cannot be named without the rest of the call: "
					+ target);
		}
		final Set<IcfgLocation> withBoundary = new HashSet<>();
		for (final L letter : letters) {
			if (finder.hasBoundary(letter)) {
				withBoundary.add(letter.getSource());
			}
		}
		final List<L> result = new ArrayList<>();
		for (final L letter : letters.subList(0, letters.size() - 1)) {
			if (!withBoundary.contains(letter.getSource())) {
				result.add(letter);
			}
		}
		result.add(target);
		return result;
	}

	/** Finds the statements where the procedure inliner has marked the start or the end of an inlined call. */
	private static final class InlinedCallBoundaryFinder extends IcfgEdgeVisitor {
		/**
		 * The key of {@code InlinedCallAnnotation}. That class is in a bundle that exports nothing and requires the C
		 * translator, which not every product with TraceAbstraction has, so it cannot be referred to from here.
		 */
		private static final String INLINED_CALL_ANNOTATION =
				"de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.InlinedCallAnnotation";

		private boolean mFound;

		private boolean hasBoundary(final IIcfgTransition<?> letter) {
			if (!(letter instanceof IcfgEdge)) {
				throw new KInductionCounterexampleException("cannot look into the letter " + letter + " of type "
						+ letter.getClass().getSimpleName());
			}
			mFound = false;
			visit((IcfgEdge) letter);
			return mFound;
		}

		@Override
		protected void visit(final StatementSequence sequence) {
			for (final Statement statement : sequence.getStatements()) {
				mFound |= statement.hasPayload() && statement.getPayload().hasAnnotation()
						&& statement.getPayload().getAnnotations().containsKey(INLINED_CALL_ANNOTATION);
			}
		}
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
