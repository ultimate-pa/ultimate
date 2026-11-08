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
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
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
	 */
	public KInduction(final IUltimateServiceProvider services, final ILogger logger, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction,
			final IInvariantSupplier<CallNode<STATE>> invariantSupplier, final boolean restartSolverAfterInterrupt)
			throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mCsToolkit = csToolkit;
		mWorkerMgdScript = csToolkit.getManagedScript();
		mLogger = logger;
		mServices = services;
		mInvariantSupplier = invariantSupplier;
		mProbation = invariantSupplier.mayInterrupt();
		mRestartSolver = restartSolverAfterInterrupt;
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
			if (verdict == Verdict.UNSAFE) {
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
			mWitness = extractWitness(k);
			mLogger.info("KInduction: violation found, model says %s", mWitness);
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
	 * Invariants for a correctness witness: for every loop head {@code h}, {@code J_h && noErrorWithinK(h)}, where
	 * {@code J_h} is the injected invariant the deciding step case assumed.
	 * <p>
	 * {@code noErrorWithinK(h)} alone is not inductive if the step case relied on injected invariants. With them
	 * it is 1-inductive: from a state that satisfies it, a successor and the next k - 1 states cannot be errors, since
	 * they are within k steps, the injected invariants hold along the way, since they are inductive themselves, and
	 * then the step case says that the k-th state cannot be an error either. Rather than trusting this argument, the
	 * invariants are checked: every transition of the system must preserve them, with {@code true} at INIT and
	 * {@code false} at FINAL. The waypoints get {@code noErrorWithinK} for that check, but no witness invariant.
	 * <p>
	 * For k = 1, {@code noErrorWithinK(h)} follows from {@code J_h} by the step case, so the invariant is just
	 * {@code J_h}, or {@code true}, and needs no quantifier elimination.
	 * <p>
	 * Must be called after the constructor, i.e. when the script is not locked: quantifier elimination uses it.
	 *
	 * @param services
	 *            for the quantifier elimination and the check of the invariants, whose timer bounds how long this may
	 *            take: once it runs out, a running check-sat is interrupted, which needs an external solver
	 * The system is flat: the invariant of a loop head of a callee may mention the variables of its callers, and a
	 * callee that is unfolded at several call sites has one loop head per call site. Whether that fits the program is
	 * for the caller to decide.
	 *
	 * @return for every loop head its invariant, quantifier-free and native to the worker's {@link ManagedScript}, or
	 *         empty if the program was not proven safe or the invariants cannot be put into a witness: a quantifier
	 *         that could not be eliminated, an old variable, or a failed check. All or nothing, since a partial
	 *         annotation is not inductive.
	 */
	public Optional<Map<CallNode<STATE>, Term>> computeWitnessInvariants(final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		if (!mSafe) {
			return Optional.empty();
		}
		final Script script = mWorkerMgdScript.getScript();
		// Throws unless the solver is an external process, the only kind whose check-sat isInductive can interrupt.
		ExternalSolverInterrupter.findScriptor(script);
		final Set<Term> oldVarConstants = new LinkedHashSet<>();
		mSystem.getOldVars().forEach(pv -> oldVarConstants.add(pv.getDefaultConstant()));
		final SubtermPropertyChecker mentionsOldVar = new SubtermPropertyChecker(oldVarConstants::contains);

		// Not the formula of a query: over term variables every shared subformula would hold its free variables, and
		// quantifier elimination does badly on the variables a step has inside.
		final BiFunction<Integer, StepVars, Term> composedStep = mSystem.composeSteps(services, mLogger, mWorkerMgdScript);
		final Map<Integer, Term> invariants = new LinkedHashMap<>();
		invariants.put(PcTransitionSystem.INIT, script.term("true"));
		invariants.put(PcTransitionSystem.FINAL, script.term("false"));
		final Map<Integer, CallNode<STATE>> nodes = new LinkedHashMap<>();
		mSystem.getHeadNodes().forEach((head, node) -> nodes.put(node, head));
		mSystem.getWaypointNodes().forEach((waypoint, node) -> nodes.put(node, waypoint));
		for (final Map.Entry<Integer, CallNode<STATE>> entry : nodes.entrySet()) {
			final int node = entry.getKey();
			final Invariant injected = mProofInvariants.get(node);
			final Term invariant;
			if (mProvedK == 1) {
				// The step case of k = 1 says that no transition leads from a state that is neither INIT nor FINAL and
				// satisfies the injected invariants to FINAL, so noErrorWithinK(node) follows from J_node, or holds
				// outright. Eliminating its quantifiers - the whole loop body, whose ite removal ran for minutes - would
				// only give back an equivalent of J_node.
				invariant = injected == null ? script.term("true") : injected.term();
			} else {
				final Term noError = noErrorWithinK(node, composedStep);
				final Term withQuantifiers = injected == null ? noError : SmtUtils.and(script, injected.term(), noError);
				// Quantifier elimination expects its input in commuhash normal form.
				invariant = PartialQuantifierElimination.eliminate(services, mWorkerMgdScript,
						CommuhashNormalFormTransformer.apply(script, withQuantifiers), simplificationTechnique);
				if (!QuantifierUtils.isQuantifierFree(invariant)) {
					return noWitness("could not eliminate the quantifiers of the invariant of %s", entry.getValue());
				}
			}
			if (mentionsOldVar.isSatisfiedBySomeSubterm(invariant)) {
				return noWitness("the invariant of %s mentions an old variable", entry.getValue());
			}
			invariants.put(node, invariant);
		}
		if (!isInductive(services, invariants, composedStep)) {
			return Optional.empty();
		}
		final Map<CallNode<STATE>, Term> result = new LinkedHashMap<>();
		mSystem.getHeadNodes().forEach((head, node) -> result.put(head, invariants.get(node)));
		mLogger.info("KInduction: invariants for a correctness witness at %d loop head(s), from k=%d", result.size(),
				mProvedK);
		return Optional.of(result);
	}

	private <T> Optional<T> noWitness(final String reason, final Object... args) {
		mLogger.warn("KInduction: no correctness witness invariants, " + reason, args);
		return Optional.empty();
	}

	/**
	 * @return whether every transition of the system leads from a state that satisfies the invariant of its source
	 *         to one that satisfies the invariant of its target
	 */
	private boolean isInductive(final IUltimateServiceProvider services, final Map<Integer, Term> invariants,
			final BiFunction<Integer, StepVars, Term> step) {
		final Script script = mWorkerMgdScript.getScript();
		mWorkerMgdScript.lock(mKILock);
		try {
			for (final List<Integer> pair : mSystem.getStepPairs()) {
				final int from = pair.get(0);
				final int to = pair.get(1);
				if (!invariants.containsKey(from) || !invariants.containsKey(to)) {
					mLogger.warn("KInduction: no correctness witness invariants, the step from node %d to %d has a node "
							+ "without one", from, to);
					return false;
				}
				final ConsecutionVars vars = new ConsecutionVars(from, to);
				final Map<Term, Term> toSuccessor = new HashMap<>();
				for (final IProgramVar pv : mSystem.getVars()) {
					toSuccessor.put(pv.getTermVariable(), vars.var(pv, 1));
				}
				final Term post = PureSubstitution.apply(mWorkerMgdScript, toSuccessor, invariants.get(to));
				final Term violation = SmtUtils.and(script, invariants.get(from),
						step.apply(0, vars), SmtUtils.not(script, post));
				mWorkerMgdScript.push(mKILock, 1);
				final LBool result;
				try {
					mWorkerMgdScript.assertTerm(mKILock, SmtUtils.quantifier(script, QuantifiedFormula.EXISTS,
							Arrays.asList(violation.getFreeVars()), violation));
					result = checkSatWithin(services, "checking that the witness invariants are inductive");
				} finally {
					mWorkerMgdScript.pop(mKILock, 1);
				}
				if (result != LBool.UNSAT) {
					mLogger.warn("KInduction: no correctness witness invariants, the transition from node %d to %d "
							+ "does not preserve them (%s)", from, to, result);
					return false;
				}
			}
		} finally {
			mWorkerMgdScript.unlock(mKILock);
		}
		return true;
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
	 * One step from the node {@code from} to the node {@code to}: step 0 has the program variables' own term
	 * variables, step 1 and the auxiliary variables are fresh.
	 */
	private final class ConsecutionVars implements StepVars {
		private final int mFrom;
		private final int mTo;
		private final Map<String, TermVariable> mFresh = new LinkedHashMap<>();

		ConsecutionVars(final int from, final int to) {
			mFrom = from;
			mTo = to;
		}

		private TermVariable fresh(final String key, final Sort sort) {
			return mFresh.computeIfAbsent(key, k -> mWorkerMgdScript.constructFreshTermVariable("kiw", sort));
		}

		@Override
		public Term var(final IProgramVar pv, final int idx) {
			return idx == 0 ? pv.getTermVariable()
					: fresh("v_" + pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
		}

		@Override
		public Term pc(final int idx) {
			return mSystem.pcValue(mWorkerMgdScript.getScript(), idx == 0 ? mFrom : mTo);
		}

		@Override
		public Term aux(final int id, final TermVariable auxVar, final int idx) {
			return fresh("aux_" + id + "_" + auxVar.getName(), auxVar.getSort());
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
	 * @return a run of the abstraction that reaches an accepting state and is feasible, i.e. a genuine counterexample.
	 *         Only defined if k-induction refuted the program.
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
