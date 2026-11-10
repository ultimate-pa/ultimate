/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.ExternalSolverInterrupter;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.ExternalSolverRestarter;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery.Invariant;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery.Kind;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem.StepVars;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.ProcedureSummaries;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystemFactory;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CounterSort;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.IndexedConstantVars;

/**
 * k-induction on a nested word automaton (path program or abstraction) that represents a program with any number of
 * loops, sequential or nested.
 * <p>
 * {@link LoopTreeFormulaBuilder} cuts the program into a tree of loops, each an acyclic graph between the places a step
 * can start and end (program start, loop heads, error states, ...). {@link PcTransitionSystem} turns this into one
 * transition system whose state is the program variables plus a program counter {@code pc}. An error is reachable iff
 * the system reaches {@code pc = FINAL}. This class runs plain k-induction on it, for {@code k = 1, 2, ...}:
 * <ul>
 * <li><b>Base case</b>: {@code pc_0 = INIT}, k transitions, {@code pc_k = FINAL} and not before. SAT means
 * (<i>unsafe</i>). Since k runs upwards, the base cases together cover every error within k steps.
 * <li><b>Step case</b>: k transitions starting in an arbitrary state that is not {@code INIT}, no error in the first k
 * states, but an error in the last one. UNSAT together with the base case for k proves that no error is reachable at
 * all (<i>safe</i>). INIT can be excluded in the first state because it has no incoming transition, so every error at a
 * step {@code > k} is preceded by k non-INIT states, and errors at steps {@code <= k} are found by the base case.
 * </ul>
 * Since the whole program, including all loop heads, is one system, a SAFE result is a genuine proof also for several
 * and for nested loops; there is no per-loop or per-path approximation. A program that is not k-inductive for any k
 * runs until the timeout; otherwise the only incompleteness is the solver returning unknown.
 * <p>
 * <b>Procedures.</b> The transition system is flat and has no call stack, so it never contains a call or a return. If
 * the abstraction has any, {@link ProcedureSummaries} resolves every call site first: a callee whose graph is loop-free
 * becomes one edge for the whole call-to-return span (and one edge per error state inside it, for a call that never
 * returns), while a callee that contains a loop is unfolded into one copy of its states per call site, so that its loop
 * becomes an ordinary nested loop of the tree and gets {@code pc} values of its own. The nodes of the tree are
 * therefore {@link CallNode}s - a state plus the call sites it was reached through - and a loop head of an unfolded
 * callee is a different head at each of its call sites. A procedure on a call cycle gets an activation record instead,
 * see {@code CallStack}.
 * <p>
 * <b>Invariant injection.</b> The {@link IInvariantSupplier} may return a trusted invariant for any loop head, also a
 * nested one. It is assumed in every unrolled state where {@code pc} is that loop head, in the base and the step case.
 * This only prunes the search and can make a loop inductive that is not k-inductive on its own, but a wrong invariant
 * makes the result wrong. An invariant that mentions a variable that occurs in no transition is dropped, which is
 * always sound. With probation, the supplier watches how long the queries take and may interrupt one that an
 * invariant made slow, after publishing a better invariant. k-induction then takes the answer of the supplier's
 * probe, or asks the query again for a violation (see {@link #answer}).
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class KInduction<LETTER extends IAction, STATE> {

	/**
	 * How long an interrupted query may take to end before its solver is killed and restarted, see
	 * {@link #restartSolverAfterInterrupt}. z3 took minutes to notice an interrupt on nonlinear arithmetic.
	 */
	private static final long KILL_GRACE_MILLIS = 1000;

	/** How often the watchdog of {@link #checkSatWithin} looks at the timer. */
	private static final long WATCHDOG_POLL_MILLIS = 100;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mWorkerMgdScript;
	private final KILock mKILock = new KILock();

	// Set by run() when the base case is satisfiable, reconstructed from mWitness by
	// KInductionCounterexampleBuilder.
	NestedRun<LETTER, STATE> mCounterexample;
	// What the model of the satisfiable base case said. Read in ask() before its pop, null unless UNSAFE.
	private KInductionWitness mWitness;
	// Instead of the two above if mWaypointsFromModel: what the model of the satisfiable base case took, per step, and
	// the letters a witness can name from it
	private final boolean mWaypointsFromModel;
	private List<List<CallNode<STATE>>> mChains;
	// Why the chains, or some of them (null in mChains), could not be read; null if they all could
	private RuntimeException mChainFailure;
	private KInductionWaypoints<LETTER, STATE> mWaypoints;

	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;
	private int mProvedK = -1;
	private Inconclusive mInconclusive;

	private final IInvariantSupplier<CallNode<STATE>> mInvariantSupplier;

	// Shared indexed-constant cache, reused across every push/pop-bracketed SAT query this instance ever issues -
	// safe because scopes are always cleanly popped between queries.
	private final Map<String, Term> mIndexedConstantsWorkerScript = new HashMap<>();

	private PcTransitionSystem<CallNode<STATE>> mSystem;
	// See PcTransitionSystemFactory.Result. Nothing else of the encoding is kept beyond the system.
	private IProgramVar mStackPointer;
	private CounterSort mStackPointerSort;
	private Set<CallNode<STATE>> mSealedStates;
	private Map<STATE, Set<STATE>> mComposedEdges;
	private Set<IProgramVar> mSyntheticVars;
	// Every program variable by its globally unique id, see programVarOfAux
	private Map<String, IProgramVar> mProgramVarsById;
	private IndexedConstantVars mConstants;
	private KInductionQuery<CallNode<STATE>> mQuery;
	// pc node of a loop head -> its invariant, over the program variables' term variables
	private final Map<Integer, Invariant> mInjectedInvariants = new LinkedHashMap<>();
	// The injected invariants the deciding step case assumed, null unless the program was proven safe
	private Map<Integer, Invariant> mProofInvariants;
	// Whether the invariant supplier may interrupt a query, see answer(), and whether a solver that died of such an
	// interrupt is restarted, see restartSolverAfterInterrupt().
	private final boolean mProbation;
	private final boolean mRestartSolver;
	// Supplied invariants that mention a variable outside the transition system, so that they are reported only once
	private final Set<Term> mUnusableInvariants = new LinkedHashSet<>();
	// Whether the supplier was asked about every loop head at least once
	private boolean mInvariantsCollected;

	/**
	 * Runs k-induction on {@code abstraction} with the solver of {@code csToolkit}.
	 *
	 * @param restartSolverAfterInterrupt
	 *            whether a solver that an interrupt of the invariant supplier killed is restarted, see
	 *            {@link #restartSolverAfterInterrupt(String)}; otherwise k-induction waits for the solver to notice the
	 *            interrupt
	 * @param waypointsFromModel
	 *            whether a violation is reported as {@link #getWaypoints()} instead of {@link #getCounterexample()}
	 */
	public KInduction(final IUltimateServiceProvider services, final ILogger logger, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction,
			final IInvariantSupplier<CallNode<STATE>> invariantSupplier, final boolean restartSolverAfterInterrupt,
			final boolean waypointsFromModel) throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mCsToolkit = csToolkit;
		mWorkerMgdScript = csToolkit.getManagedScript();
		mLogger = logger;
		mServices = services;
		mInvariantSupplier = invariantSupplier;
		mProbation = invariantSupplier.mayInterrupt();
		mRestartSolver = restartSolverAfterInterrupt;
		mWaypointsFromModel = waypointsFromModel;
		run();
	}

	private enum Verdict {
		SAFE, UNSAFE, UNKNOWN
	}

	private void run() throws AutomataLibraryException {
		mLogger.info("KInduction: starting k-induction");
		// Building the loop tree composes transition formulas, which declares constants for their aux vars and thus
		// locks the script itself. So the tree has to be complete before we take the lock for the solver queries.
		mStackPointerSort = CounterSort.forProgram(mWorkerMgdScript.getScript(), mCsToolkit);
		final PcTransitionSystemFactory.Result<STATE> encoding;
		try {
			encoding = PcTransitionSystemFactory.build(mServices, mLogger, mCsToolkit, mWorkerMgdScript, mAbstraction,
					mStackPointerSort);
		} catch (final RuntimeException | Error e) {
			mInvariantSupplier.systemFailed(e);
			throw e;
		}
		mSystem = encoding.system();
		mStackPointer = encoding.stackPointer();
		mSealedStates = encoding.sealedStates();
		mComposedEdges = encoding.composedEdges();
		mSyntheticVars = encoding.syntheticVars();
		mInvariantSupplier.systemBuilt(mSystem, mWorkerMgdScript);
		mLogger.info(
				"KInduction: transition system with %d pc value(s), %d edge(s), %d variable(s), %d loop head(s), "
						+ "counters of sort %s",
				mSystem.getNumNodes(), mSystem.getNumEdges(), mSystem.getVars().size(),
				mSystem.getHeadNodes().size(), mSystem.getCounterSort());
		mLogger.info("KInduction: encoding statistics: %s", mSystem.getStatistics());

		mWorkerMgdScript.lock(mKILock);
		try {
			mConstants = new IndexedConstantVars(mWorkerMgdScript.getScript(), mIndexedConstantsWorkerScript,
					"ki", mSystem.getCounterSort());
			mQuery = new KInductionQuery<>(mSystem, mWorkerMgdScript, mKILock, mConstants, true);
			if (mProbation) {
				final Script script = mWorkerMgdScript.getScript();
				// Throws unless the solver is an external process, the only kind that can be interrupted.
				ExternalSolverInterrupter.findScriptor(script);
				// Killing the solver needs the restart; without it, k-induction waits for the solver to notice.
				final long grace = mRestartSolver ? KILL_GRACE_MILLIS : -1;
				mInvariantSupplier.setInterrupter(() -> ExternalSolverInterrupter.interrupt(script, grace));
			}

			final Verdict verdict = kInduction();
			mSafe = verdict == Verdict.SAFE;
			mSolverReturnedUnknown = verdict == Verdict.UNKNOWN;
			if (verdict == Verdict.UNSAFE && mWaypointsFromModel) {
				mWaypoints = new KInductionWaypoints<>(mAbstraction, mChains, mChainFailure, mComposedEdges,
						mStackPointer != null);
				if (mWaypoints.getLevel() != KInductionWaypoints.Level.FULL) {
					mLogger.warn("KInduction: the waypoints of the model are only good for a witness at level %s (%s)",
							mWaypoints.getLevel(), mWaypoints.getDegradeCause());
				}
				if (mWaypoints.isErrorStateGuessed()) {
					mLogger.warn("KInduction: the model does not say which error state it reaches, reporting %s",
							mWaypoints.getErrorState());
				}
				mLogger.info("KInduction: %d waypoint letter(s) from the model, %d state(s) without one",
						mWaypoints.getLetters().size(), mWaypoints.getNumSuppressedStates());
			} else if (verdict == Verdict.UNSAFE) {
				// Still under the lock, but after the base case's pop: reconstruction asserts terms, which would
				// invalidate the model we are working from. mWitness already holds everything we need from it.
				mCounterexample = new KInductionCounterexampleBuilder<>(mServices, mLogger, mWorkerMgdScript, mKILock,
						mCsToolkit, mAbstraction, mSystem, mWitness, mSealedStates).build();
			}
		} finally {
			mWorkerMgdScript.unlock(mKILock);
		}
		mLogger.info("is safe " + mSafe);
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	private Verdict kInduction() {
		for (int k = 1;; k++) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "k-induction at k=" + k);
			}
			// The supplier may have learned more since the last k; asking never waits.
			collectInvariants();
			final LBool base = answer(Kind.BASE, k);
			mLogger.info("KInduction: k=%d - base case: %s", k, base);
			if (base == LBool.SAT) {
				return Verdict.UNSAFE;
			}
			if (base == LBool.UNKNOWN) {
				mInconclusive = Inconclusive.solverUnknown(k, "base");
				return Verdict.UNKNOWN;
			}
			// The step case of k is larger than the base case of k, so check the deadline again.
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "k-induction at k=" + k + ", before the step case");
			}
			final LBool step = answer(Kind.STEP, k);
			mLogger.info("KInduction: k=%d - step case: %s", k, step);
			mLogger.info("KInduction: k=%d - last step of DAG size %d, %d constants, DAG size sent so far %d", k,
					mQuery.getLastStepDagSize(), mIndexedConstantsWorkerScript.size(), mQuery.getAssertedDagSize());
			if (step == LBool.UNSAT) {
				mProvedK = k;
				// What the deciding step case assumed: a correctness witness has to assume it too.
				mProofInvariants = new LinkedHashMap<>(mInjectedInvariants);
				return Verdict.SAFE;
			}
			if (step == LBool.UNKNOWN) {
				mInconclusive = Inconclusive.solverUnknown(k, "step");
				return Verdict.UNKNOWN;
			}
			// step case SAT: not yet inductive, unroll once more
		}
	}

	/**
	 * Asks the query of {@code kind} for {@code k} until it is answered. The invariant supplier may abort a query that
	 * one of its invariants makes slow; it publishes a better invariant first, so the query is asked again with what
	 * the supplier has now.
	 */
	private LBool answer(final Kind kind, final int k) {
		while (true) {
			mInvariantSupplier.queryStarted(kind, k);
			final long start = System.nanoTime();
			final LBool result = ask(kind, k);
			mInvariantSupplier.queryFinished(kind, k, (System.nanoTime() - start) / 1_000_000);
			if (result != null) {
				return result;
			}
			// The supplier published weaker invariants before the abort; the next query is to use them.
			collectInvariants();
			final Optional<LBool> probed = mInvariantSupplier.takeAnswer(kind, k);
			// Sound for either answer: invariants hold in every reachable state, so the base case does not depend on
			// them, and a step case that is unsat with weaker invariants is unsat with stronger ones; sat only means
			// to go on with k + 1. Only a violation is asked again, since its witness is read from this solver's model.
			if (probed.isPresent() && !(kind == Kind.BASE && probed.get() == LBool.SAT)) {
				mLogger.info("KInduction: the invariant supplier aborted the %s case at k=%d and answered it: %s",
						kind, k, probed.get());
				return probed.get();
			}
			mLogger.info("KInduction: the invariant supplier aborted the %s case at k=%d, asking it again", kind, k);
		}
	}

	/**
	 * Asks the query of {@code kind} for {@code k} once. A satisfiable base case is a violation, whose witness is read
	 * from the model before the pop.
	 *
	 * @return the answer, or {@code null} if the invariant supplier aborted the query
	 */
	private LBool ask(final Kind kind, final int k) {
		final List<Term> invariants = mQuery.prepare(k, mInjectedInvariants);
		mWorkerMgdScript.push(mKILock, 1);
		mQuery.assertQuery(kind, k, invariants);
		if (kind == Kind.BASE && mStackPointer != null) {
			// A run starts with an empty stack, see CallStack. The probation's base case does without: its unsat holds
			// here as well, and its sat is asked again here.
			final Script script = mWorkerMgdScript.getScript();
			mWorkerMgdScript.assertTerm(mKILock, SmtUtils.binaryEquality(script, mConstants.var(mStackPointer, 0),
					mStackPointerSort.value(script, 0)));
		}
		final LBool result = checkSat();
		if (result == LBool.SAT && kind == Kind.BASE) {
			// The model dies with this scope, so it has to be read now. The constants themselves were declared by
			// prepare(k), i.e. outside the push, and survive the pop.
			if (mWaypointsFromModel) {
				mChains = readChains(k);
			} else {
				mWitness = extractWitness(k);
				mLogger.info("KInduction: violation found, model says %s", mWitness);
			}
		}
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
	}

	/**
	 * @return the answer, or {@code null} if the invariant supplier interrupted the query
	 */
	private LBool checkSat() {
		final LBool result;
		try {
			result = mWorkerMgdScript.checkSat(mKILock);
		} catch (final SMTLIBException e) {
			if (restartSolverAfterInterrupt(e.getMessage())) {
				return null;
			}
			throw e;
		}
		if (result == LBool.UNKNOWN && mProbation
				&& ExternalSolverInterrupter.wasInterrupted(mWorkerMgdScript.getScript())) {
			// The solver may have answered the interrupt just before it was killed for being too slow.
			if (ExternalSolverInterrupter.wasKilled(mWorkerMgdScript.getScript())
					&& !restartSolverAfterInterrupt("killed after answering the interrupt")) {
				throw new SMTLIBException("the solver of k-induction was killed after an interrupt, but it may not "
						+ "be restarted");
			}
			return null;
		}
		return result;
	}

	/**
	 * An interrupt of the invariant supplier kills the solver if it arrives just after the solver answered, or if the
	 * solver does not notice it within {@link #KILL_GRACE_MILLIS}. Restarts the solver with the declarations and the
	 * stack it had, but no assertions; k-induction then takes the supplier's answer or asks the query again, and the
	 * next query sends all its steps again. Remove this method, its call and the grace period to drop the restart.
	 *
	 * @param reason
	 *            why the solver is to be restarted, for the log
	 * @return whether the solver was restarted, false if it was not interrupted, so that its failure has another cause
	 */
	private boolean restartSolverAfterInterrupt(final String reason) {
		if (!mProbation || !mRestartSolver || !ExternalSolverInterrupter.wasInterrupted(mWorkerMgdScript.getScript())) {
			return false;
		}
		mLogger.warn("KInduction: the solver died of an interrupt (%s), restarting it", reason);
		ExternalSolverRestarter.restartAndReplay(mWorkerMgdScript.getScript());
		mQuery.solverRestarted();
		return true;
	}

	/**
	 * Reads the chain of cut-graph states that the model of a satisfiable base case takes in every step. Must be called
	 * after {@code checkSat} returned {@code sat} and before the {@code pop} of that query. FINAL only stutters, so a step
	 * that starts there has no chain.
	 * <p>
	 * The violation is proved by the {@code sat} alone, the chains only make its witness. So a chain that cannot be read
	 * is null in the result, and none at all is null, with the first reason in {@link #mChainFailure}: the witness then
	 * says less (see {@link KInductionWaypoints.Level}), but the verdict stands. A timeout still ends k-induction.
	 */
	private List<List<CallNode<STATE>>> readChains(final int k) {
		final Script script = mWorkerMgdScript.getScript();
		final int[] pcValues;
		try {
			pcValues = readPcValues(script, k);
		} catch (final ToolchainCanceledException e) {
			throw e;
		} catch (final RuntimeException e) {
			mLogger.warn("KInduction: violation found, but the pc values of the model cannot be read (%s), the witness "
					+ "names no waypoint", e);
			mChainFailure = e;
			return null;
		}
		mLogger.info("KInduction: violation found, pc sequence of the model: %s", Arrays.toString(pcValues));
		final StepVars declared = mConstants.declaredOnly();
		final List<List<CallNode<STATE>>> chains = new ArrayList<>(k);
		for (int j = 0; j < k && pcValues[j] != PcTransitionSystem.FINAL; j++) {
			try {
				chains.add(mSystem.getChainOfStep(j, pcValues[j], pcValues[j + 1], declared, mWorkerMgdScript,
						term -> holdsInModel(script, term)));
			} catch (final ToolchainCanceledException e) {
				throw e;
			} catch (final RuntimeException e) {
				mLogger.warn("KInduction: could not read the chain of step %d (%s), the witness names at most the "
						+ "target", j, e);
				if (mChainFailure == null) {
					mChainFailure = e;
				}
				chains.add(null);
			}
		}
		return chains;
	}

	/**
	 * The value of one closed formula in the current model. Asked for one formula at a time because a solver may print
	 * the formulas of a {@code get-value} differently from how it got them, so that an answer about several compound
	 * formulas cannot be told apart.
	 */
	private boolean holdsInModel(final Script script, final Term formula) {
		if (SmtUtils.isTrueLiteral(formula) || SmtUtils.isFalseLiteral(formula)) {
			return SmtUtils.isTrueLiteral(formula);
		}
		final Map<Term, Term> answer = getValues(script, List.of(formula));
		if (answer.size() != 1) {
			throw new IllegalStateException("The solver gave " + answer.size() + " values for one formula");
		}
		final Term value = answer.values().iterator().next();
		if (!SmtUtils.isTrueLiteral(value) && !SmtUtils.isFalseLiteral(value)) {
			throw new IllegalStateException("The solver gave the value " + value + " for a formula");
		}
		return SmtUtils.isTrueLiteral(value);
	}

	private int[] readPcValues(final Script script, final int k) {
		final List<Term> queried = new ArrayList<>();
		for (int j = 0; j <= k; j++) {
			queried.add(mConstants.pc(j));
		}
		final Map<Term, Term> model = getValues(script, queried);
		final int[] pcValues = new int[k + 1];
		for (int j = 0; j <= k; j++) {
			pcValues[j] = mSystem.getCounterSort().toInt(model.get(mConstants.pc(j)), "pc_" + j);
		}
		return pcValues;
	}

	/**
	 * Reads the model of a satisfiable base case: the pc and the stack pointer of every state, and the values
	 * {@link KInductionWitness} describes. Must be called after {@code checkSat} returned {@code sat} and before the
	 * {@code pop} of that query. Asks for the values of constants the query declared only, see
	 * {@link IndexedConstantVars#declaredOnly()}.
	 */
	private KInductionWitness extractWitness(final int k) {
		final Script script = mWorkerMgdScript.getScript();
		final List<Term> queried = new ArrayList<>();
		for (int j = 0; j <= k; j++) {
			queried.add(mConstants.pc(j));
		}
		if (mStackPointer != null) {
			for (int j = 0; j <= k; j++) {
				queried.add(mConstants.var(mStackPointer, j));
			}
		}
		final Map<Term, Term> model = getValues(script, queried);

		final int[] pcValues = new int[k + 1];
		for (int j = 0; j <= k; j++) {
			pcValues[j] = mSystem.getCounterSort().toInt(model.get(mConstants.pc(j)), "pc_" + j);
		}
		int[] stackPointers = null;
		if (mStackPointer != null) {
			stackPointers = new int[k + 1];
			for (int j = 0; j <= k; j++) {
				stackPointers[j] = mStackPointerSort.toInt(model.get(mConstants.var(mStackPointer, j)),
						mStackPointer + "_" + j);
			}
		}

		// The values the counterexample is replayed with. Now that the pc is known, only what is live is asked for.
		// Only sorts whose values a solver reports as literals; arrays, which z3 may report as a function of its model
		// (as-array), are left out, as everywhere in Ultimate (see SmtUtils.isSortForWhichWeCanGetValues).
		final StepVars declared = mConstants.declaredOnly();
		final boolean[] fullyPinned = new boolean[k + 1];
		final List<Map<IProgramVar, Term>> pinConstants = new ArrayList<>();
		final List<Map<IProgramVar, List<Term>>> versionConstants = new ArrayList<>();
		final Set<Term> values = new LinkedHashSet<>();
		for (int j = 0; j <= k; j++) {
			final Map<IProgramVar, Term> pins = new LinkedHashMap<>();
			fullyPinned[j] = true;
			for (final IProgramVar pv : mSystem.getLiveVars(pcValues[j])) {
				final Term constant = declared.var(pv, j);
				if (constant == null || mSyntheticVars.contains(pv)) {
					// No constant: no query mentions it, so nothing constrains it. Synthetic: no run of letters has it.
					continue;
				}
				if (!SmtUtils.isSortForWhichWeCanGetValues(constant.getSort())) {
					fullyPinned[j] = false;
					continue;
				}
				pins.put(pv, constant);
				values.add(constant);
			}
			pinConstants.add(pins);
			if (j < k) {
				final Map<IProgramVar, List<Term>> versions = new LinkedHashMap<>();
				mSystem.getVersionConstants(j, declared).forEach((pv, terms) -> versions.put(pv, new ArrayList<>(terms)));
				for (final Map.Entry<TermVariable, List<Term>> aux : mSystem.getAuxConstants(j, declared).entrySet()) {
					final IProgramVar pv = programVarOfAux(aux.getKey());
					if (pv != null) {
						versions.computeIfAbsent(pv, x -> new ArrayList<>()).addAll(aux.getValue());
					}
				}
				versions.keySet().removeAll(mSyntheticVars);
				versions.keySet().removeIf(pv -> !SmtUtils.isSortForWhichWeCanGetValues(pv.getTermVariable().getSort()));
				versions.values().forEach(values::addAll);
				versionConstants.add(versions);
			}
		}
		final Map<IProgramConst, Term> constantTerms = new LinkedHashMap<>();
		for (final IProgramConst constant : mCsToolkit.getSymbolTable().getConstants()) {
			if (!SmtUtils.isSortForWhichWeCanGetValues(constant.getDefaultConstant().getSort())) {
				continue;
			}
			constantTerms.put(constant, constant.getDefaultConstant());
			values.add(constant.getDefaultConstant());
		}
		final Map<Term, Term> valueModel = getValues(script, values);

		final List<Map<IProgramVar, Term>> pins = new ArrayList<>();
		for (int j = 0; j <= k; j++) {
			final Map<IProgramVar, Term> pinned = new LinkedHashMap<>();
			for (final Map.Entry<IProgramVar, Term> pin : pinConstants.get(j).entrySet()) {
				final Term value = valueModel.get(pin.getValue());
				if (isClosedLiteral(value)) {
					pinned.put(pin.getKey(), value);
				} else {
					fullyPinned[j] = false;
				}
			}
			// A variable live here that the query never mentions has no constant at all; nothing constrains it.
			pins.add(pinned);
		}
		final List<Map<IProgramVar, List<Term>>> candidates = new ArrayList<>();
		for (int j = 0; j < k; j++) {
			final Map<IProgramVar, Set<Term>> distinct = new LinkedHashMap<>();
			for (final Map.Entry<IProgramVar, List<Term>> versions : versionConstants.get(j).entrySet()) {
				for (final Term constant : versions.getValue()) {
					final Term value = valueModel.get(constant);
					if (isClosedLiteral(value)) {
						distinct.computeIfAbsent(versions.getKey(), x -> new LinkedHashSet<>()).add(value);
					}
				}
			}
			// What a variable holds at the end of the step is a value it had inside it, too.
			for (final Map.Entry<IProgramVar, Term> pin : pins.get(j + 1).entrySet()) {
				distinct.computeIfAbsent(pin.getKey(), x -> new LinkedHashSet<>()).add(pin.getValue());
			}
			final Map<IProgramVar, List<Term>> candidatesOfStep = new LinkedHashMap<>();
			distinct.forEach((pv, terms) -> candidatesOfStep.put(pv, new ArrayList<>(terms)));
			candidates.add(candidatesOfStep);
		}
		final Map<IProgramConst, Term> constants = new LinkedHashMap<>();
		for (final Map.Entry<IProgramConst, Term> constant : constantTerms.entrySet()) {
			final Term value = valueModel.get(constant.getValue());
			if (isClosedLiteral(value)) {
				constants.put(constant.getKey(), value);
			}
		}
		return new KInductionWitness(k, pcValues, stackPointers, pins, fullyPinned, candidates, constants);
	}

	/**
	 * The program variable an auxiliary variable of a composed transition formula stands for: composing names the
	 * value a variable has in between {@code v_<globally unique id>_<n>}, see
	 * {@code ManagedScript.constructFreshTermVariable}. {@code null} for any other auxiliary variable. Only used to
	 * guess values, so a wrong match costs a try, nothing else.
	 */
	private IProgramVar programVarOfAux(final TermVariable aux) {
		if (mProgramVarsById == null) {
			mProgramVarsById = new HashMap<>();
			for (final IProgramVar pv : mCsToolkit.getSymbolTable().getGlobals()) {
				mProgramVarsById.put(pv.getGloballyUniqueId(), pv);
			}
			for (final String procedure : mCsToolkit.getProcedures()) {
				for (final IProgramVar pv : mCsToolkit.getSymbolTable().getLocals(procedure)) {
					mProgramVarsById.put(pv.getGloballyUniqueId(), pv);
				}
			}
		}
		final String name = aux.getName();
		final int index = name.lastIndexOf('_');
		if (!name.startsWith("v_") || index <= 2 || !name.substring(index + 1).chars().allMatch(Character::isDigit)) {
			return null;
		}
		return mProgramVarsById.get(name.substring(2, index));
	}

	private Map<Term, Term> getValues(final Script script, final Collection<Term> terms) {
		try {
			// Not ManagedScript.getValue: SmtUtils normalizes what the solver returns, e.g. z3's (- 1) to -1.
			return SmtUtils.getValues(script, terms);
		} catch (final UnsupportedOperationException e) {
			throw new UnsupportedOperationException("k-induction found a violation but the solver cannot produce a "
					+ "model, so no counterexample can be extracted. The worker's solver needs a mode that sets "
					+ ":produce-models (e.g. External_ModelsAndUnsatCoreMode, the default).", e);
		}
	}

	/**
	 * Whether a value from a model means the same outside it: a term without variables that only uses the functions of
	 * the theories. z3's {@code (_ as-array k!0)}, for example, names a function of its model and is no such term.
	 */
	private static boolean isClosedLiteral(final Term value) {
		if (value == null || value.getFreeVars().length > 0) {
			return false;
		}
		final Deque<Term> todo = new ArrayDeque<>();
		todo.push(value);
		while (!todo.isEmpty()) {
			final Term current = todo.pop();
			if (current instanceof ConstantTerm) {
				continue;
			}
			if (!(current instanceof final ApplicationTerm app) || !app.getFunction().isIntern()) {
				return false;
			}
			for (final Term param : app.getParameters()) {
				todo.push(param);
			}
		}
		return true;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Invariant injection
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Asks the supplier for an invariant of every loop head and keeps those that only mention variables of the
	 * transition system. Never waits: if the supplier has nothing new since the last call, nothing changes.
	 */
	private void collectInvariants() {
		if (!mInvariantSupplier.update() && mInvariantsCollected) {
			return;
		}
		mInvariantsCollected = true;
		for (final Map.Entry<CallNode<STATE>, Integer> head : mSystem.getHeadNodes().entrySet()) {
			final Optional<Term> invariant = mInvariantSupplier.getInvariant(head.getKey(), mWorkerMgdScript);
			// Terms are unified by the script, so an unchanged invariant is the very same object.
			final Invariant injected = mInjectedInvariants.get(head.getValue());
			if (invariant.isEmpty() || injected != null && invariant.get() == injected.term()
					|| mUnusableInvariants.contains(invariant.get())) {
				continue;
			}
			final Map<IProgramVar, TermVariable> used = mQuery.variablesOf(invariant.get());
			if (used == null) {
				mUnusableInvariants.add(invariant.get());
				mLogger.info("KInduction: ignoring invariant of loop head %s, it mentions a variable which occurs in "
						+ "no transition", head.getKey());
				continue;
			}
			mInjectedInvariants.put(head.getValue(), new Invariant(invariant.get(), used));
			mLogger.info("KInduction: using invariant of loop head %s: %s", head.getKey(), invariant.get());
		}
	}

	/**
	 * Not (exists a run of {@link #mProvedK} transitions from {@code node} that ends in FINAL), over the term variables
	 * of the program variables. Since FINAL only has its stutter loop, this says that no error is reachable from
	 * {@code node} within k steps.
	 *
	 * @param step
	 *            the relation of one step over the given variables
	 */
	private Term noErrorWithinK(final int node, final BiFunction<Integer, StepVars, Term> step) {
		final Script script = mWorkerMgdScript.getScript();
		final FreshVars vars = new FreshVars(node);
		final List<Term> conjuncts = new ArrayList<>();
		for (int j = 0; j < mProvedK; j++) {
			conjuncts.add(step.apply(j, vars));
		}
		conjuncts.add(SmtUtils.binaryEquality(script, vars.pc(mProvedK),
				mSystem.pcValue(script, PcTransitionSystem.FINAL)));
		final Term reachError = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, vars.getFreshVariables(),
				SmtUtils.and(script, conjuncts));
		return SmtUtils.not(script, reachError);
	}

	// ------------------------------------------------------------------------------------------------------------
	// Correctness witness
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * How long the quantifier elimination of {@code noErrorWithinK} may take for a witness, for all loop heads and
	 * waypoints together, see {@link #strengthenWithNoErrorWithinK}.
	 */
	private static final long WITNESS_QE_TIMEOUT_MILLIS = 5_000;
	/** How much longer it is waited for when it does not notice its timer. */
	private static final long WITNESS_QE_GRACE_MILLIS = 500;

	/** Name of the flags of {@link #houdini}, indexed by the position of their candidate in a round. */
	private static final String WITNESS_FLAG_NAME = "kiwrefuted";

	/**
	 * An annotation of the pc nodes of loop heads and waypoints that {@link #houdini} proved inductive, with
	 * {@code true} at INIT and at every node without an entry.
	 *
	 * @param invariants
	 *            the conjuncts of the invariant of each node, over the program variables' term variables
	 * @param safe
	 *            whether the annotation also proves the program: no step from a node other than FINAL that satisfies
	 *            its invariant reaches FINAL
	 */
	private record InductiveAnnotation(Map<Integer, Set<Term>> invariants, boolean safe) {
	}

	/** {@code flag} is true iff the step ends at the pc node {@code node} and violates {@code candidate}. */
	private record WitnessFlag(int node, Term candidate, Term flag) {
	}

	// The full-frame step of the inductiveness checks over mConstants, built on the first use
	private Term mWitnessStep;
	// The best invariants for a correctness witness found so far, by loop head; null until there are some. Written by
	// the thread that computes them, read by the worker when it stops waiting for that thread.
	private volatile Map<STATE, Term> mBestWitnessInvariants;

	/**
	 * Invariants for a correctness witness, one per loop head, all proven inductive on the transition system.
	 * <p>
	 * Every annotation this returns is inductive: INIT has {@code true}, and every step from a node whose invariant
	 * holds leads to a node whose invariant holds. Each invariant therefore holds in every reachable state at its loop
	 * head, whether or not the annotation also proves the program, and any subset of them is a valid witness.
	 * <ol>
	 * <li>For k = 1 without injected invariants, the step case assumed nothing: {@code true} at every loop head is
	 * inductive and proves the program. Without supplied candidates (step 2), that is the result.
	 * <li>The candidates are the conjuncts of the injected invariants the deciding step case assumed, and the invariant
	 * supplier's candidates for witness invariants ({@link IInvariantSupplier#getWitnessCandidates}), which the proof did
	 * not need but make the witness stronger. {@link #houdini} keeps the largest inductive subset, which contains the
	 * injected invariants if they are inductive on their own. For k = 1 they prove the program.
	 * <li>For k &gt; 1 they usually do not. Then each node gets {@code noErrorWithinK} as further candidates, computed by
	 * quantifier elimination. From a state that satisfies {@code J && noErrorWithinK}, a successor and the next k - 1
	 * states cannot be errors, since they are within k steps, the injected invariants J hold along the way, since they
	 * are inductive themselves, and the step case says that the k-th state cannot be an error either. So together they
	 * are 1-inductive, and {@link #houdini} checks it. The quantifier elimination gets
	 * {@link #WITNESS_QE_TIMEOUT_MILLIS}; if it does not end in time, or the timer runs out during this step, the result
	 * of step 2 stands.
	 * </ol>
	 * The result of every step that is done is also kept for {@link #getBestWitnessInvariants()}, for a caller that stops
	 * waiting: quantifier elimination does not always notice the timer.
	 * <p>
	 * Must be called after the constructor, i.e. when the script is not locked: quantifier elimination uses it.
	 * <p>
	 * The system is flat: the invariant of a loop head of a callee may mention the variables of its callers, and a
	 * callee that is unfolded at several call sites has one loop head per call site. The result is by loop head state:
	 * conjuncts out of scope there are left out, and the call nodes of a state get the disjunction of their invariants.
	 *
	 * @param services
	 *            for the quantifier elimination and the inductiveness checks, whose timer bounds how long this may take:
	 *            once it runs out, a running check-sat is interrupted, which needs an external solver
	 * @param inScope
	 *            whether a variable may occur in the invariant of a loop head state, i.e. is in scope at its location
	 * @return for every loop head state its invariant, quantifier-free and native to the worker's
	 *         {@link ManagedScript}, or empty if the program was not proven safe or the solver could not decide whether
	 *         the candidates are inductive
	 * @throws ToolchainCanceledException
	 *             if the timer ran out before any annotation was proven inductive
	 */
	public Optional<Map<STATE, Term>> computeWitnessInvariants(final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final BiPredicate<STATE, TermVariable> inScope) {
		if (!mSafe) {
			return Optional.empty();
		}
		final long start = System.nanoTime();
		final Map<Integer, Set<Term>> injected = injectedCandidates();
		final Map<Integer, Set<Term>> candidates = suppliedCandidates(injected);
		mLogger.info("KInduction witness: proof at k=%d, %d injected and %d supplied candidate conjunct(s)", mProvedK,
				countConjuncts(injected), countConjuncts(candidates) - countConjuncts(injected));
		Map<STATE, Term> result = null;
		if (mProvedK == 1 && injected.isEmpty()) {
			// The step case of k = 1 assumed nothing, so true at every loop head is inductive and proves the program.
			mLogger.info("KInduction witness: k=1 without injected invariants, every loop head gets true");
			result = publishWitness(Collections.emptyMap(), true, inScope, start);
			if (candidates.isEmpty()) {
				return Optional.of(result);
			}
		}
		// Throws unless the solver is an external process, the only kind whose check-sat houdini can interrupt.
		ExternalSolverInterrupter.findScriptor(mWorkerMgdScript.getScript());

		// Without candidates there is nothing to check: true everywhere is inductive, and for k > 1 it does not prove
		// the program, or the step case of k = 1 would have.
		final InductiveAnnotation checked;
		try {
			checked = candidates.isEmpty() ? new InductiveAnnotation(Collections.emptyMap(), false)
					: houdini(services, candidates, "injected and supplied invariants");
		} catch (final ToolchainCanceledException e) {
			if (result == null) {
				throw e;
			}
			mLogger.warn("KInduction witness: the timer ran out while checking the supplied invariants after %d ms, "
					+ "keeping true", elapsedMillis(start));
			return Optional.of(result);
		}
		if (checked == null) {
			return Optional.ofNullable(result);
		}
		result = publishWitness(checked.invariants(), checked.safe(), inScope, start);
		if (checked.safe() || mProvedK == 1) {
			return Optional.of(result);
		}
		final Map<Integer, Set<Term>> strengthened =
				strengthenWithNoErrorWithinK(services, simplificationTechnique, checked.invariants());
		if (strengthened == null) {
			return Optional.of(result);
		}
		try {
			final InductiveAnnotation withNoError = houdini(services, strengthened, "with noErrorWithinK");
			if (withNoError != null) {
				result = publishWitness(withNoError.invariants(), withNoError.safe(), inScope, start);
			}
		} catch (final ToolchainCanceledException e) {
			mLogger.warn("KInduction witness: the timer ran out while checking noErrorWithinK after %d ms, keeping "
					+ "the invariants without it", elapsedMillis(start));
		}
		return Optional.of(result);
	}

	/**
	 * @return the best invariants for a correctness witness that {@link #computeWitnessInvariants} has found so far, by
	 *         loop head; null if it has not proven any yet. Safe to call from another thread.
	 */
	public Map<STATE, Term> getBestWitnessInvariants() {
		return mBestWitnessInvariants;
	}

	/** @return the k of the deciding step case, -1 unless the program was proven safe */
	public int getProvedK() {
		return mProvedK;
	}

	/**
	 * @return the conjuncts of the injected invariants the deciding step case assumed, per pc node, without {@code true}
	 *         and without those that mention an old variable, which a witness cannot express at a loop head
	 */
	private Map<Integer, Set<Term>> injectedCandidates() {
		final Map<Integer, Set<Term>> candidates = new LinkedHashMap<>();
		for (final Map.Entry<Integer, Invariant> entry : mProofInvariants.entrySet()) {
			addConjuncts(candidates, entry.getKey(), entry.getValue().term());
		}
		return candidates;
	}

	/**
	 * @return {@code injected} together with the invariant supplier's candidates for witness invariants at every loop
	 *         head and waypoint, which the proof did not need: what the supplier learned after the proof, what it
	 *         withheld from k-induction, and what it could not prove yet. None of them is trusted, {@link #houdini}
	 *         checks them.
	 */
	private Map<Integer, Set<Term>> suppliedCandidates(final Map<Integer, Set<Term>> injected) {
		final Map<Integer, Set<Term>> candidates = new LinkedHashMap<>();
		injected.forEach((node, conjuncts) -> candidates.put(node, new LinkedHashSet<>(conjuncts)));
		final Map<CallNode<STATE>, Integer> nodes = new LinkedHashMap<>(mSystem.getHeadNodes());
		nodes.putAll(mSystem.getWaypointNodes());
		for (final Map.Entry<CallNode<STATE>, Integer> entry : nodes.entrySet()) {
			for (final Term supplied : mInvariantSupplier.getWitnessCandidates(entry.getKey(), mWorkerMgdScript)) {
				addConjuncts(candidates, entry.getValue(), supplied);
			}
		}
		return candidates;
	}

	private void addConjuncts(final Map<Integer, Set<Term>> candidates, final int node, final Term invariant) {
		final Set<Term> oldVarConstants = new LinkedHashSet<>();
		mSystem.getOldVars().forEach(pv -> oldVarConstants.add(pv.getDefaultConstant()));
		final SubtermPropertyChecker mentionsOldVar = new SubtermPropertyChecker(oldVarConstants::contains);
		for (final Term conjunct : SmtUtils.getConjuncts(invariant)) {
			if (SmtUtils.isTrueLiteral(conjunct)) {
				continue;
			}
			if (mentionsOldVar.isSatisfiedBySomeSubterm(conjunct)) {
				mLogger.info("KInduction witness: dropping the candidate %s of node %d, it mentions an old variable",
						conjunct, node);
				continue;
			}
			if (mQuery.variablesOf(conjunct) == null) {
				mLogger.info("KInduction witness: dropping the candidate %s of node %d, it mentions a variable "
						+ "which occurs in no transition", conjunct, node);
				continue;
			}
			candidates.computeIfAbsent(node, x -> new LinkedHashSet<>()).add(conjunct);
		}
	}

	/**
	 * Adds the conjuncts of {@code noErrorWithinK} to {@code annotation} at every loop head and waypoint whose
	 * quantifiers can be eliminated within {@link #WITNESS_QE_TIMEOUT_MILLIS}, for all of them together. If the timer
	 * runs out, the nodes done so far keep what they got. Quantifier elimination does not always notice the timer (its
	 * ite removal ran for minutes), so it runs on a thread of its own, and if it has not ended
	 * {@link #WITNESS_QE_GRACE_MILLIS} after the timer, it is left behind.
	 *
	 * @return the strengthened annotation, or null if the quantifier elimination was left behind: it still uses the
	 *         script, so nothing else may use it any more
	 */
	private Map<Integer, Set<Term>> strengthenWithNoErrorWithinK(final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final Map<Integer, Set<Term>> annotation) {
		final IProgressMonitorService monitor = services.getProgressMonitorService();
		final IUltimateServiceProvider qeServices =
				monitor.registerChildTimer(services, monitor.getChildTimer(WITNESS_QE_TIMEOUT_MILLIS));
		final FutureTask<Map<Integer, Set<Term>>> task =
				new FutureTask<>(() -> eliminateNoErrorWithinK(qeServices, simplificationTechnique, annotation));
		final Thread thread = new Thread(task, "KInduction witness quantifier elimination");
		thread.setDaemon(true);
		thread.start();
		try {
			return task.get(WITNESS_QE_TIMEOUT_MILLIS + WITNESS_QE_GRACE_MILLIS, TimeUnit.MILLISECONDS);
		} catch (final TimeoutException e) {
			thread.interrupt();
			mLogger.warn("KInduction witness: the quantifier elimination of noErrorWithinK did not end within %d ms, "
					+ "keeping the invariants without it", WITNESS_QE_TIMEOUT_MILLIS + WITNESS_QE_GRACE_MILLIS);
			return null;
		} catch (final InterruptedException e) {
			thread.interrupt();
			Thread.currentThread().interrupt();
			throw new ToolchainCanceledException(getClass(), "waiting for the quantifier elimination of noErrorWithinK");
		} catch (final ExecutionException e) {
			if (e.getCause() instanceof final RuntimeException runtime) {
				throw runtime;
			}
			if (e.getCause() instanceof final Error error) {
				throw error;
			}
			throw new AssertionError("eliminateNoErrorWithinK threw a checked exception", e.getCause());
		}
	}

	/**
	 * The work of {@link #strengthenWithNoErrorWithinK}, on its thread.
	 */
	private Map<Integer, Set<Term>> eliminateNoErrorWithinK(final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final Map<Integer, Set<Term>> annotation) {
		final Script script = mWorkerMgdScript.getScript();
		final long phaseStart = System.nanoTime();
		final Map<Integer, Set<Term>> result = new LinkedHashMap<>();
		annotation.forEach((node, conjuncts) -> result.put(node, new LinkedHashSet<>(conjuncts)));
		try {
			// Not the formula of a query: over term variables every shared subformula would hold its free variables,
			// and quantifier elimination does badly on the variables a step has inside.
			final BiFunction<Integer, StepVars, Term> composedStep =
					mSystem.composeSteps(services, mLogger, mWorkerMgdScript);
			mLogger.info("KInduction witness: composed the steps in %d ms", elapsedMillis(phaseStart));
			final Set<Integer> nodes = new LinkedHashSet<>(mSystem.getHeadNodes().values());
			nodes.addAll(mSystem.getWaypointNodes().values());
			for (final int node : nodes) {
				final long start = System.nanoTime();
				final Term noError = noErrorWithinK(node, composedStep);
				final Set<Term> known = annotation.getOrDefault(node, Collections.emptySet());
				// The known invariant is context for the simplification; its conjuncts come back and are already there.
				final Term withQuantifiers = SmtUtils.and(script, SmtUtils.and(script, known), noError);
				// Quantifier elimination expects its input in commuhash normal form.
				final Term eliminated = PartialQuantifierElimination.eliminate(services, mWorkerMgdScript,
						CommuhashNormalFormTransformer.apply(script, withQuantifiers), simplificationTechnique);
				if (!QuantifierUtils.isQuantifierFree(eliminated)) {
					mLogger.info("KInduction witness: node %d keeps its invariant, the quantifiers of noErrorWithinK "
							+ "could not be eliminated (%d ms)", node, elapsedMillis(start));
					continue;
				}
				mLogger.info("KInduction witness: noErrorWithinK of node %d in %d ms, DAG size %d", node,
						elapsedMillis(start), PcTransitionSystem.dagSize(eliminated));
				addConjuncts(result, node, eliminated);
			}
		} catch (final ToolchainCanceledException e) {
			mLogger.warn("KInduction witness: the quantifier elimination of noErrorWithinK ran out of its %d ms after "
					+ "%d ms, keeping what it found so far", WITNESS_QE_TIMEOUT_MILLIS, elapsedMillis(phaseStart));
		}
		return result;
	}

	/**
	 * Houdini: the largest subset of {@code candidates} that is inductive, with {@code true} at INIT. One query checks
	 * all remaining candidates at once:
	 *
	 * <pre>
	 *   AND_node (pc_0 = node  ->  candidates(node))  at step 0
	 *   and step(0)
	 *   and AND_(node,c) (b_(node,c) = (pc_1 = node and not c))  at step 1
	 *   and OR_(node,c) b_(node,c)
	 * </pre>
	 *
	 * If it is satisfiable, the candidates whose flag is true in the model are dropped and the query is repeated; each
	 * round drops at least one. The model is only asked for the flags, which parse back as themselves, see
	 * {@code InductivenessChecker}. A last query asks whether a step from a node other than FINAL leads to FINAL.
	 * <p>
	 * Every query is quantifier-free: the variables of the two states are the constants of k-induction's steps 0 and 1.
	 *
	 * @param phase
	 *            what the candidates are, for the log
	 * @return the inductive subset, or null if the solver could not decide a query
	 */
	private InductiveAnnotation houdini(final IUltimateServiceProvider services,
			final Map<Integer, Set<Term>> candidates, final String phase) {
		final long start = System.nanoTime();
		final Script script = mWorkerMgdScript.getScript();
		final Map<Integer, Set<Term>> remaining = new LinkedHashMap<>();
		candidates.forEach((node, conjuncts) -> remaining.put(node, new LinkedHashSet<>(conjuncts)));
		final int numCandidates = countConjuncts(remaining);
		final Term pc0 = mConstants.pc(0);
		final Term pc1 = mConstants.pc(1);
		final Term fin = mSystem.pcValue(script, PcTransitionSystem.FINAL);
		int rounds = 0;
		mWorkerMgdScript.lock(mKILock);
		try {
			// Everything that declares a constant has to happen before the push, see IndexedConstantVars.
			if (mWitnessStep == null) {
				mWitnessStep = mSystem.step(0, mConstants, mWorkerMgdScript);
			}
			while (true) {
				final List<Term> pre = witnessPreconditions(remaining);
				final List<WitnessFlag> flags = new ArrayList<>();
				final List<Term> definitions = new ArrayList<>();
				for (final Map.Entry<Integer, Set<Term>> entry : remaining.entrySet()) {
					final Term atNode = SmtUtils.binaryEquality(script, pc1, mSystem.pcValue(script, entry.getKey()));
					for (final Term candidate : entry.getValue()) {
						final Term flag = PredicateUtils.getIndexedConstant(WITNESS_FLAG_NAME,
								SmtSortUtils.getBoolSort(script), flags.size(), mIndexedConstantsWorkerScript, script);
						flags.add(new WitnessFlag(entry.getKey(), candidate, flag));
						definitions.add(SmtUtils.binaryEquality(script, flag,
								SmtUtils.and(script, atNode, SmtUtils.not(script, instantiate(candidate, 1)))));
					}
				}
				if (flags.isEmpty()) {
					break;
				}
				rounds++;
				final LBool result;
				mWorkerMgdScript.push(mKILock, 1);
				try {
					mWorkerMgdScript.assertTerm(mKILock, mWitnessStep);
					for (final Term term : pre) {
						mWorkerMgdScript.assertTerm(mKILock, term);
					}
					for (final Term term : definitions) {
						mWorkerMgdScript.assertTerm(mKILock, term);
					}
					mWorkerMgdScript.assertTerm(mKILock,
							SmtUtils.or(script, flags.stream().map(WitnessFlag::flag).toList()));
					result = checkSatWithin(services, "checking that the witness invariants are inductive");
					if (result == LBool.SAT) {
						dropRefuted(remaining, flags);
					}
				} finally {
					mWorkerMgdScript.pop(mKILock, 1);
				}
				if (result == LBool.UNSAT) {
					break;
				}
				if (result == LBool.UNKNOWN) {
					mLogger.warn("KInduction witness: the solver could not decide whether the %s are inductive", phase);
					return null;
				}
			}
			remaining.values().removeIf(Set::isEmpty);

			final List<Term> pre = witnessPreconditions(remaining);
			final LBool safety;
			mWorkerMgdScript.push(mKILock, 1);
			try {
				mWorkerMgdScript.assertTerm(mKILock, mWitnessStep);
				for (final Term term : pre) {
					mWorkerMgdScript.assertTerm(mKILock, term);
				}
				mWorkerMgdScript.assertTerm(mKILock, SmtUtils.not(script, SmtUtils.binaryEquality(script, pc0, fin)));
				mWorkerMgdScript.assertTerm(mKILock, SmtUtils.binaryEquality(script, pc1, fin));
				safety = checkSatWithin(services, "checking that the witness invariants exclude errors");
			} finally {
				mWorkerMgdScript.pop(mKILock, 1);
			}
			final boolean safe = safety == LBool.UNSAT;
			mLogger.info("KInduction witness: %s: %d of %d candidate conjunct(s) inductive after %d round(s), %s, %d ms",
					phase, countConjuncts(remaining), numCandidates, rounds,
					safe ? "they prove the program" : "they do not prove the program (" + safety + ")",
					elapsedMillis(start));
			return new InductiveAnnotation(remaining, safe);
		} finally {
			mWorkerMgdScript.unlock(mKILock);
		}
	}

	/** @return for every node of {@code annotation}: at step 0, if pc is that node, its invariant holds */
	private List<Term> witnessPreconditions(final Map<Integer, Set<Term>> annotation) {
		final Script script = mWorkerMgdScript.getScript();
		final List<Term> result = new ArrayList<>();
		for (final Map.Entry<Integer, Set<Term>> entry : annotation.entrySet()) {
			if (entry.getValue().isEmpty()) {
				continue;
			}
			final List<Term> instantiated = new ArrayList<>();
			for (final Term conjunct : entry.getValue()) {
				instantiated.add(instantiate(conjunct, 0));
			}
			result.add(SmtUtils.implies(script,
					SmtUtils.binaryEquality(script, mConstants.pc(0), mSystem.pcValue(script, entry.getKey())),
					SmtUtils.and(script, instantiated)));
		}
		return result;
	}

	/** {@code term} over the program variables' term variables, as a term over the constants of step {@code idx}. */
	private Term instantiate(final Term term, final int idx) {
		final Map<IProgramVar, TermVariable> vars = mQuery.variablesOf(term);
		if (vars == null) {
			throw new IllegalArgumentException(term + " mentions a variable that is no variable of the system");
		}
		final Map<Term, Term> substitution = new HashMap<>();
		vars.forEach((pv, tv) -> substitution.put(tv, mConstants.var(pv, idx)));
		return PureSubstitution.apply(mWorkerMgdScript, substitution, term);
	}

	/** Reads the model of a satisfiable round of {@link #houdini}: drops the candidates whose flag is true. */
	private void dropRefuted(final Map<Integer, Set<Term>> remaining, final List<WitnessFlag> flags) {
		final Map<Term, Term> values =
				SmtUtils.getValues(mWorkerMgdScript.getScript(), flags.stream().map(WitnessFlag::flag).toList());
		boolean dropped = false;
		for (final WitnessFlag flag : flags) {
			final Term value = values.get(flag.flag());
			if (value == null) {
				throw new AssertionError("the model has no value for the flag " + flag.flag() + " of "
						+ flag.candidate() + " at node " + flag.node() + ", only for " + values.keySet());
			}
			if (SmtUtils.isTrueLiteral(value)) {
				remaining.get(flag.node()).remove(flag.candidate());
				dropped = true;
			} else if (!SmtUtils.isFalseLiteral(value)) {
				throw new AssertionError("the model gives " + value + " for the flag " + flag.flag() + " of "
						+ flag.candidate() + " at node " + flag.node() + ", not a Boolean literal");
			}
		}
		if (!dropped) {
			throw new AssertionError("the model satisfies the query, but gives the flag of every candidate the value "
					+ "false");
		}
	}

	/**
	 * Makes {@code annotation} the best witness so far, by loop head state. Every invariant of an inductive annotation
	 * holds on its own, and so does every conjunct of it, so the conjuncts that mention a variable out of scope at the
	 * loop head are left out. A loop head with several call nodes (a callee unfolded at several call sites) gets the
	 * disjunction of their invariants, since each of them holds whenever control is at that call node.
	 *
	 * @param inScope
	 *            whether a variable is in scope at a loop head state
	 * @return its invariants by loop head state, {@code true} where it has none
	 */
	private Map<STATE, Term> publishWitness(final Map<Integer, Set<Term>> annotation, final boolean safe,
			final BiPredicate<STATE, TermVariable> inScope, final long start) {
		final Script script = mWorkerMgdScript.getScript();
		final Map<STATE, List<Term>> byState = new LinkedHashMap<>();
		int outOfScope = 0;
		for (final Map.Entry<CallNode<STATE>, Integer> head : mSystem.getHeadNodes().entrySet()) {
			final STATE state = head.getKey().getState();
			final List<Term> conjuncts = new ArrayList<>();
			for (final Term conjunct : annotation.getOrDefault(head.getValue(), Collections.emptySet())) {
				if (Arrays.stream(conjunct.getFreeVars()).allMatch(tv -> inScope.test(state, tv))) {
					conjuncts.add(conjunct);
				} else {
					outOfScope++;
				}
			}
			byState.computeIfAbsent(state, x -> new ArrayList<>()).add(SmtUtils.and(script, conjuncts));
		}
		final Map<STATE, Term> result = new LinkedHashMap<>();
		int nonTrivial = 0;
		int severalCallNodes = 0;
		for (final Map.Entry<STATE, List<Term>> entry : byState.entrySet()) {
			if (entry.getValue().size() > 1) {
				severalCallNodes++;
			}
			final Term invariant = SmtUtils.or(script, entry.getValue());
			if (!SmtUtils.isTrueLiteral(invariant)) {
				nonTrivial++;
			}
			result.put(entry.getKey(), invariant);
		}
		mBestWitnessInvariants = Collections.unmodifiableMap(result);
		mLogger.info("KInduction witness: %d of %d loop head(s) non-trivial, from k=%d, %s, after %d ms "
				+ "(%d conjunct(s) out of scope left out, %d loop head(s) with several call nodes)", nonTrivial,
				result.size(), mProvedK, safe ? "proving the program" : "not proving the program", elapsedMillis(start),
				outOfScope, severalCallNodes);
		return mBestWitnessInvariants;
	}

	private static int countConjuncts(final Map<Integer, Set<Term>> annotation) {
		return annotation.values().stream().mapToInt(Set::size).sum();
	}

	private static long elapsedMillis(final long startNanos) {
		return (System.nanoTime() - startNanos) / 1_000_000;
	}

	/**
	 * A check-sat that ends with the timer of {@code services}. The solver's own per-query timeout is that of
	 * k-induction, up to an hour, and a running check-sat never looks at the timer, so a watchdog thread interrupts
	 * it once the timer runs out. Must be called with the lock held.
	 *
	 * @param task
	 *            what the check is for, reported if the timer ran out
	 * @throws ToolchainCanceledException
	 *             if the timer ran out before or during the check
	 */
	private LBool checkSatWithin(final IUltimateServiceProvider services, final String task) {
		final IProgressMonitorService monitor = services.getProgressMonitorService();
		if (!monitor.continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), task);
		}
		final Script script = mWorkerMgdScript.getScript();
		final Thread watchdog = new Thread(() -> {
			try {
				while (monitor.continueProcessing()) {
					Thread.sleep(WATCHDOG_POLL_MILLIS);
				}
				ExternalSolverInterrupter.interrupt(script, KILL_GRACE_MILLIS);
			} catch (final InterruptedException e) {
				// The check-sat ended first.
			}
		}, "KInduction check-sat watchdog");
		watchdog.setDaemon(true);
		watchdog.start();
		final LBool result;
		try {
			result = mWorkerMgdScript.checkSat(mKILock);
		} catch (final SMTLIBException e) {
			// The interrupt killed the solver because it did not answer within the grace period.
			if (!monitor.continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), task + " (" + e.getMessage() + ")");
			}
			throw e;
		} finally {
			watchdog.interrupt();
			joinWatchdog(watchdog);
		}
		// An interrupted check-sat answers unknown; that is the timer, not the solver giving up.
		if (!monitor.continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), task);
		}
		return result;
	}

	/**
	 * Waits until the watchdog is gone, so that an interrupt it is just sending cannot hit a later query.
	 */
	private static void joinWatchdog(final Thread watchdog) {
		boolean interrupted = false;
		while (true) {
			try {
				watchdog.join();
				break;
			} catch (final InterruptedException e) {
				interrupted = true;
			}
		}
		if (interrupted) {
			Thread.currentThread().interrupt();
		}
	}

	/**
	 * Unrolling with fresh term variables, for a formula with quantifiers. Step 0 is the loop head {@code node} with
	 * the program variables' own term variables (the convention of {@link IInvariantSupplier}); all later steps and
	 * auxiliary variables are fresh and are to be quantified, see {@link #getFreshVariables()}.
	 */
	private final class FreshVars implements StepVars {
		private final int mNode;
		private final Map<String, TermVariable> mFresh = new LinkedHashMap<>();
		private final Set<TermVariable> mFreshVariables = new LinkedHashSet<>();

		FreshVars(final int node) {
			mNode = node;
		}

		Set<TermVariable> getFreshVariables() {
			return mFreshVariables;
		}

		private TermVariable fresh(final String key, final Sort sort) {
			return mFresh.computeIfAbsent(key, k -> {
				final TermVariable tv = mWorkerMgdScript.constructFreshTermVariable("ki", sort);
				mFreshVariables.add(tv);
				return tv;
			});
		}

		@Override
		public Term var(final IProgramVar pv, final int idx) {
			if (idx == 0) {
				return pv.getTermVariable();
			}
			return fresh("v_" + pv.getGloballyUniqueId() + "_" + idx, pv.getTermVariable().getSort());
		}

		@Override
		public Term pc(final int idx) {
			final Script script = mWorkerMgdScript.getScript();
			if (idx == 0) {
				return mSystem.pcValue(script, mNode);
			}
			return fresh("pc_" + idx, mSystem.getCounterSort().getSort());
		}

		@Override
		public Term aux(final int id, final TermVariable auxVar, final int idx) {
			return fresh("aux_" + id + "_" + auxVar.getName() + "_" + idx, auxVar.getSort());
		}
	}

	public boolean isSafe() {
		return mSafe;
	}

	public boolean wasUnkown() {
		return mSolverReturnedUnknown;
	}

	/**
	 * @return why k-induction ended without a verdict. Only defined if {@link #wasUnkown()}.
	 */
	public Inconclusive getInconclusive() {
		if (mInconclusive == null) {
			throw new UnsupportedOperationException(
					"k-induction was not inconclusive, so there is no reason to report");
		}
		return mInconclusive;
	}

	/**
	 * Why k-induction stopped without proving or refuting the program: the solver answered {@code unknown}, and it will
	 * keep doing so until the query itself changes (fewer variables, a different encoding, an injected invariant, or a
	 * higher resource limit).
	 */
	public static final class Inconclusive {
		private final int mK;
		private final String mCase;

		private Inconclusive(final int k, final String theCase) {
			mK = k;
			mCase = theCase;
		}

		static Inconclusive solverUnknown(final int k, final String theCase) {
			return new Inconclusive(k, theCase);
		}

		public int getK() {
			return mK;
		}

		@Override
		public String toString() {
			return "k-induction is inconclusive: the solver returned unknown for the " + mCase + " case at k=" + mK
					+ ", so the program is neither proved safe nor refuted";
		}
	}

	/**
	 * @return the letters a violation witness can name. Only defined if k-induction refuted the program with waypoints
	 *         from the model.
	 */
	public KInductionWaypoints<LETTER, STATE> getWaypoints() {
		if (mWaypoints == null) {
			throw new IllegalStateException("k-induction did not refute the program with waypoints from the model");
		}
		return mWaypoints;
	}

	/**
	 * @return a run of the abstraction that reaches an accepting state and is feasible, i.e. a genuine counterexample.
	 *         Only defined if k-induction refuted the program without waypoints from the model.
	 */
	public NestedRun<LETTER, STATE> getCounterexample() {
		if (mSafe || mSolverReturnedUnknown) {
			throw new UnsupportedOperationException(
					"k-induction did not refute the program, so there is no " + "counterexample");
		}
		if (mCounterexample == null) {
			throw new IllegalStateException("k-induction refuted the program but no counterexample was built; "
					+ "KInductionCounterexampleBuilder must either return a run or throw");
		}
		return mCounterexample;
	}

	/**
	 * Package private class used by KInduction to lock the {@link ManagedScript}.
	 */
	static class KILock {
	}
}
