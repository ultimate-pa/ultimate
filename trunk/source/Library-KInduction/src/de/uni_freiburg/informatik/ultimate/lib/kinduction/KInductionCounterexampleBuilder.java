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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallStack;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.ProcedureSummaries;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor.Execution;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor.StepKind;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor.Successor;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.NondeterminismPool;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.UnsupportedTermException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Turns a {@link KInductionWitness} - what the solver's model of a satisfiable base case said - into a concrete
 * {@link NestedRun} of the abstraction that reaches an accepting state, by replaying the violation on the values of the
 * model. The solver is only asked where those values leave something open.
 *
 * <h2>What has to be found</h2>
 *
 * A step of the {@link PcTransitionSystem} is not a single letter. It is a <em>path</em> through one scope's cut graph,
 * whose edges are composed from letters where a chain or a whole call-to-return span was summarized
 * ({@link ProcedureSummaries}). The model pins down the pc at every step, but not which letters a step took: at every
 * state of the abstraction with more than one outgoing transition, it has to be found out which one the violation
 * takes.
 *
 * <h2>Replaying the model</h2>
 *
 * The model fixes the values the violation has at the start of every step, see {@link KInductionWitness}: the
 * <b>pins</b>, the values of all variables that are live there, are exactly the values of the path the model took.
 * The run starts from the pins of the first state, and every letter is <b>executed</b> on the values the run has, in
 * plain Java ({@link ConcreteTransFormulaExecutor}, the interpreter of the value analysis):
 * <ul>
 * <li>a state with one useful outgoing transition simply takes it;
 * <li>at a state with several, the guards decide on the concrete values, so only the transitions that can be taken are
 * followed;
 * <li>a havoced variable stays without a value until it is read. The interpreter then chooses its value, one variable
 * at a time and dropping a choice as soon as a conjunct of the letter contradicts it: from what the letter's own
 * equalities say, for an array from the cells the letter fixes, and otherwise from the model's <b>candidates</b> for
 * this step - the values the variable has inside the step, then every other value of its sort there. A variable that
 * the step cannot write again tries its pin first: that is exactly the value it has from here on, while most of the
 * values inside the step belong to paths the model did not take.
 * </ul>
 * At the end of a step the run must have the pins of the next state. A step that misses one does not continue the way
 * the model did, and is not taken. A variable the run has no value for yet takes the pin's.
 *
 * <h2>Where the solver comes in</h2>
 *
 * Where executing cannot decide, the letter is taken <b>symbolically</b>, as in a trace check: what it writes becomes a
 * fresh constant, its formula is asserted over the values and constants of what it reads, and the solver - the one
 * k-induction used, so it handles every theory the encoding has - decides. That happens if a havoced value the letter
 * reads is not among the candidates (or no candidate makes the run reach the pins), if the letter reads such a constant,
 * and if the interpreter cannot evaluate the formula (floating point, say). The symbolic way is always tried after the
 * concrete ones, so the search is complete. The solver is only asked to check satisfiability where the run branches and
 * at the end of a step, never for a state with a single useful transition.
 * <p>
 * Once a step has reached the pins, the run is <b>committed</b> to them: every constant still open takes the value of
 * the solver's model (if it has a sort the solver reports values of, see {@link KInductionWitness}; an array stays
 * open), and the next step starts concrete again. That is sound because the pins are all the next step
 * can read: every variable that is not pinned is written before it is read. It is not done where this does not hold:
 * at a state some of whose pins the model could not give (see {@link KInductionWitness#isFullyPinned}), and in a
 * program with a {@link CallStack}, whose saved activations the pins only cover through the stack arrays, which a run
 * of letters does not have. There the constants stay open and the search may backtrack into earlier steps.
 * <p>
 * Every run that comes back was executed or checked by the solver letter for letter, so it is feasible as a whole and
 * ends in an accepting state. {@link #assemble} re-checks it with {@code Accepts}, and
 * {@code KInductionWorkerThread.reportCounterexample} independently confirms it with the ordinary trace check. If
 * the encoding were ever to report a violation that does not exist, no run would be found and this class would throw
 * rather than invent one.
 *
 * <h2>Calls</h2>
 *
 * A pc step can contain a whole call-to-return span, so the search walks call and return transitions as well, with
 * a stack of the call sites it has entered; a return is only ever taken with the hierarchical predecessor that
 * stack names, which is what makes the reconstructed word properly nested. The values mirror what
 * {@code TransFormulaUtils.sequentialCompositionWithCallAndReturn} did to the formula the model was produced from:
 * at a call the parameters are assigned, every oldvar of a global the callee may modify gets that global's current
 * value, and every local of the callee that is not an inparam has no value (it is arbitrary at procedure entry); at
 * the return the result is assigned and the callee's scope - those oldvars and locals - is restored to what the caller
 * saw. An oldvar that no call on the stack assigns is read as {@code getDefaultConstant()}, as a step of
 * {@code PcTransitionSystem} starts with it.
 * <p>
 * A step ends at the target nodes of its pc value. Each such node carries the call sites it stands for, so
 * a step over a <em>summarized</em> call ends back in the caller with an empty stack, while a step inside an
 * <em>unfolded</em> callee ends with exactly that callee's call sites still open - its loop heads are pc values of
 * their own, so ending there is normal. A violation inside a summarized callee is the one node that says less than
 * the stack does: {@link ProcedureSummaries} resolves it into an edge into the callee's error state, which names
 * only the direct call site although the error may lie several summarized levels deeper, so the run ends there with
 * those calls still pending and the nested word gets unmatched call positions.
 *
 * <h2>How far the search may wander</h2>
 *
 * Per step the letter path is <b>simple, except that its last state may equal its first</b>. A cut graph is
 * acyclic, and all of a scope's own heads and the heads of its inner loops are sealed in it - they are nodes but
 * have no outgoing edges - so such a state can only ever be a path's last. The exception is what a loop body needs:
 * a step in a loop scope can run from a head back to the same head. A state visited inside a call is a different
 * search node from the same state visited outside it, since the two differ in what the run may do next, so "simple"
 * is meant with respect to the call stack. Without recursion that keeps the search finite. With recursion the call
 * stack alone would not, so a step may open at most one call per procedure, plus one: a recursive cycle contains a loop
 * head, and a step can pass one only as its first and last state.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class KInductionCounterexampleBuilder<LETTER extends IAction, STATE> {

	/**
	 * How many successors the interpreter yields for one letter and one choice of the values it reads. Not a limit of
	 * the search: the symbolic way is tried after them, whatever they were.
	 */
	private static final int CONCRETE_SUCCESSORS_PER_LETTER = 64;

	/** Enough of the stuck state's outgoing transitions to see what went wrong, without flooding the log. */
	private static final int MAX_SUCCESSORS_IN_MESSAGE = 8;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final Object mLockOwner;
	private final CfgSmtToolkit mCsToolkit;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final PcTransitionSystem<CallNode<STATE>> mSystem;
	private final KInductionWitness mWitness;
	/**
	 * The nodes that stand for an error inside a <em>summarized</em> callee, see
	 * {@link ProcedureSummaries#getSealedStates()}. They are the one case in which a pc step may end with calls
	 * still open that the node itself does not name: the summary of a call-to-return span is a single edge, so an
	 * error several summarized levels down is reached with that whole chain of calls pending.
	 */
	private final Set<CallNode<STATE>> mSummarizedErrorTargets;

	/** The number of pc steps to reconstruct. */
	private final int mSteps;

	private final ModelCandidatePool mPool = new ModelCandidatePool();
	private final ConcreteTransFormulaExecutor mExecutor =
			new ConcreteTransFormulaExecutor(mPool, CONCRETE_SUCCESSORS_PER_LETTER);
	/** The model's literals as values of the interpreter, empty for one it cannot read (e.g. floating point). */
	private final Map<Term, Optional<IConcreteValue>> mValueOfLiteral = new HashMap<>();
	private final Map<Pair<Integer, IProgramVar>, List<IConcreteValue>> mCandidateValues = new HashMap<>();
	private final Map<Pair<Integer, IProgramVar>, List<IConcreteValue>> mPinFirstCandidates = new HashMap<>();
	/** Per target pc and state, what a step towards that pc can still write from the state on. */
	private final Map<Pair<Integer, STATE>, Set<IProgramVar>> mWrittenFrom = new HashMap<>();
	/** The value of every program constant the model gave one. */
	private final Map<IProgramConst, IConcreteValue> mConstantValues = new HashMap<>();

	/** How far the search ever got, for the message of a search that then failed. */
	private int mDeepestStep = -1;
	private STATE mDeepestState;
	private int mDeepestOpenCalls;
	/** The longest letter path the search ever had, i.e. how far it got inside a step. */
	private int mFurthestLetters = -1;
	private STATE mFurthestLetterState;
	private int mFurthestLetterStep = -1;
	/** Why the deepest step that reached a target node could not end there. */
	private String mDeepestPinMismatch;
	private int mDeepestPinMismatchStep = -1;

	// The run being built. All four are undone on backtracking.
	private final List<LETTER> mLetters = new ArrayList<>();
	private final List<STATE> mStates = new ArrayList<>();
	private final List<Integer> mNesting = new ArrayList<>();
	private final List<Boolean> mTakenSymbolically = new ArrayList<>();

	/** The calls the search has entered and not yet left. */
	private final Deque<Frame> mStack = new ArrayDeque<>();

	/**
	 * What the run knows about each variable. A variable without an entry has no value yet: it was havoced, or never
	 * assigned, and its first read chooses one.
	 */
	private final Map<IProgramVar, Slot> mCurrent = new HashMap<>();
	private final Map<String, Term> mCexConstants = new HashMap<>();
	private int mSsaCounter;
	private int mAuxCounter;
	/** Whether something was asserted since the solver last said sat. */
	private boolean mUnchecked;

	private int mExpansions;
	private int mCheckSats;
	private int mCommits;

	/** How many scopes we have pushed. A successful search returns with its whole stack standing; see build(). */
	private int mPushDepth;

	// state -> states reachable from it, computed lazily per target pc value
	private final Map<Integer, Set<STATE>> mCanReachTarget = new HashMap<>();
	private Map<STATE, List<STATE>> mPredecessors;
	private Set<IProgramVar> mOldVarsRead;

	/** What the run knows about a variable: a value, or a constant of the solver that stands for one. */
	private sealed interface Slot permits Known, Symbolic {
		/** The slot as a term: the value's literal, or the constant. */
		Term term(Script script);
	}

	/**
	 * A value. The interpreter's value is {@code null} for a literal it cannot read (floating point, say), which only
	 * the solver can work with; the literal is built from the value only when it is needed, since a memory array can
	 * be large.
	 */
	private static final class Known implements Slot {
		private final IConcreteValue mValue;
		private final Sort mSort;
		private Term mLiteral;

		private Known(final IConcreteValue value, final Sort sort) {
			mValue = value;
			mSort = sort;
		}

		private Known(final Term literal, final IConcreteValue value) {
			mValue = value;
			mSort = literal.getSort();
			mLiteral = literal;
		}

		@Override
		public Term term(final Script script) {
			if (mLiteral == null) {
				mLiteral = mValue.toTerm(script, mSort);
			}
			return mLiteral;
		}
	}

	/** A constant of the solver; what the letters asserted about it is what the run knows. */
	private record Symbolic(Term constant) implements Slot {
		@Override
		public Term term(final Script script) {
			return constant;
		}
	}

	/** A pin or another literal of the model as a slot. */
	private Known known(final Term literal) {
		return new Known(literal, valueOf(literal));
	}

	/**
	 * One entered call: where it was made, which letter position it is, and what the run knew about everything the
	 * call overwrote (the callee's locals and the oldvars of the globals it may modify), so that the return can put
	 * the caller's view back. A {@code null} slot means the variable had no value.
	 */
	private final class Frame {
		private final STATE mCallSite;
		private final int mCallPosition;
		private final Map<IProgramVar, Slot> mCalleeScope;

		private Frame(final STATE callSite, final int callPosition, final Map<IProgramVar, Slot> calleeScope) {
			mCallSite = callSite;
			mCallPosition = callPosition;
			mCalleeScope = calleeScope;
		}
	}

	/** What stays fixed while the letter path of one pc step is searched for. */
	private final class Step {
		private final int mIndex;
		/** The nodes the step can end at. */
		private final Set<CallNode<STATE>> mTargets;
		/** The state the step started in; the only state the path may return to, and only as its last. */
		private final STATE mFirst;
		/** The search nodes (state plus open calls) already on this step's path. */
		private final Set<Object> mVisited = new LinkedHashSet<>();
		/** The states from which a target of the step is still reachable. */
		private final Set<STATE> mUseful;
		/** How many calls may be open during this step, see the class javadoc. */
		private final int mMaxOpenCalls;

		private Step(final int index, final STATE first) {
			final int targetPc = mWitness.getPc(index + 1);
			mIndex = index;
			mTargets = mSystem.getTargetStates(targetPc);
			mFirst = first;
			mUseful = canReachATargetOf(targetPc);
			mMaxOpenCalls = mStack.size() + mCsToolkit.getProcedures().size() + 1;
			mVisited.add(nodeAfter(first, null, false));
		}
	}

	private enum Kind {
		INTERNAL, CALL, RETURN
	}

	/** A transition the search could take next. */
	private final class Move {
		private final LETTER mLetter;
		private final STATE mSucc;
		private final Kind mKind;
		/** The search node the letter leads to, i.e. the successor plus the calls open after it. */
		private final Object mNode;

		private Move(final LETTER letter, final STATE succ, final Kind kind, final Object node) {
			mLetter = letter;
			mSucc = succ;
			mKind = kind;
			mNode = node;
		}
	}

	/** One way to take a move: what it does to the run, and what it asserts if it is taken symbolically. */
	private final class Alternative {
		private final Move mMove;
		private final boolean mSymbolic;
		/**
		 * The slots of variables the letter read without the run having a value for them. Kept apart from
		 * {@link #mUpdates} because a call's frame restores exactly what the call updated at the return, while a
		 * global first read at the call has to keep its value after the return.
		 */
		private final Map<IProgramVar, Slot> mReads = new LinkedHashMap<>();
		/** The new slot of every variable the letter writes; {@code null} means it has no value afterwards. */
		private final Map<IProgramVar, Slot> mUpdates = new LinkedHashMap<>();
		/** The letter's formula over the run's slots, {@code null} for a letter that was executed. */
		private Term mAssertion;

		private Alternative(final Move move, final boolean symbolic) {
			mMove = move;
			mSymbolic = symbolic;
		}
	}

	/** The values of a step's model candidates, for the variables a letter leaves open. */
	private final class ModelCandidatePool extends NondeterminismPool {
		private Step mStep;
		/** The state the letter being executed leads to. */
		private STATE mSuccessor;

		@Override
		public List<IConcreteValue> preferred(final IProgramVar var, final Sort sort) {
			if (var == null) {
				return List.of();
			}
			return writtenFrom(mStep, mSuccessor).contains(var) ? candidateValues(mStep.mIndex, var)
					: pinFirstCandidates(mStep.mIndex, var);
		}
	}

	public KInductionCounterexampleBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final Object lockOwner, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction,
			final PcTransitionSystem<CallNode<STATE>> system, final KInductionWitness witness,
			final Set<CallNode<STATE>> summarizedErrorTargets) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mLockOwner = lockOwner;
		mCsToolkit = csToolkit;
		mAbstraction = abstraction;
		mSystem = system;
		mWitness = witness;
		mSummarizedErrorTargets = summarizedErrorTargets;
		mSteps = witness.getK();
	}

	/**
	 * @return a feasible run of the abstraction into an accepting state.
	 * @throws KInductionCounterexampleException
	 *             if the violation cannot be expressed as a run of the abstraction.
	 */
	public NestedRun<LETTER, STATE> build() {
		checkWitnessShape();
		mLogger.info("KInduction: reconstructing a counterexample for %d pc step(s) of %s", mSteps, mWitness);
		for (final Map.Entry<IProgramConst, Term> constant : mWitness.getConstants().entrySet()) {
			final IConcreteValue value = valueOf(constant.getValue());
			if (value != null) {
				mConstantValues.put(constant.getKey(), value);
			}
		}

		push();
		try {
			final Set<STATE> starts = statesOf(mSystem.getSourceStates(mWitness.getPc(0)));
			for (final STATE start : starts) {
				if (!mAbstraction.isInitial(start)) {
					continue;
				}
				mStates.add(start);
				mCurrent.clear();
				for (final Map.Entry<IProgramVar, Term> pin : mWitness.getPins(0).entrySet()) {
					mCurrent.put(pin.getKey(), known(pin.getValue()));
				}
				if (solveFrom(0, start)) {
					return assemble();
				}
				mLetters.clear();
				mStates.clear();
				mNesting.clear();
				mTakenSymbolically.clear();
				mStack.clear();
			}
			throw noRunFound("no counterexample run starts in any of the initial states " + starts
					+ ", although k-induction reported a violation at k=" + mWitness.getK() + " (" + mWitness + ")");
		} finally {
			// A search that succeeded returns with every scope it pushed still on the stack, so unwind by depth
			// rather than by a fixed count.
			while (mPushDepth > 0) {
				pop();
			}
		}
	}

	private void push() {
		mMgdScript.push(mLockOwner, 1);
		mPushDepth++;
	}

	private void pop() {
		mMgdScript.pop(mLockOwner, 1);
		mPushDepth--;
	}

	private LBool checkSat() {
		mCheckSats++;
		final LBool result = mMgdScript.checkSat(mLockOwner);
		if (result == LBool.UNKNOWN) {
			throw new KInductionCounterexampleException("the solver returned unknown while reconstructing a "
					+ "counterexample for " + mWitness + ", so it cannot tell which way the violation goes");
		}
		return result;
	}

	/** The parts of the witness this class relies on, checked once so a later failure is not misattributed. */
	private void checkWitnessShape() {
		if (mWitness.getPc(0) != PcTransitionSystem.INIT) {
			throw new AssertionError("the base case asserts pc_0 = INIT, but the model says pc_0 = "
					+ mWitness.getPc(0));
		}
		if (mWitness.getPc(mSteps) != PcTransitionSystem.FINAL) {
			throw new AssertionError("the base case asserts pc_" + mSteps + " = FINAL, but the model says pc_" + mSteps
					+ " = " + mWitness.getPc(mSteps));
		}
	}

	/**
	 * Continues the search at the start of pc step {@code step}, with the run at that step's boundary.
	 *
	 * @return true if the whole remaining counterexample was found; the solver stack is then left as it is.
	 */
	private boolean solveFrom(final int step, final STATE state) {
		if (step > mDeepestStep) {
			// Only ever grows, so a failed search can say how far it did get. Without it every failure looks like
			// "the very first step is impossible", which is almost never where the two encodings actually part.
			mDeepestStep = step;
			mDeepestState = state;
			mDeepestOpenCalls = mStack.size();
		}
		if (step == mSteps) {
			// endStep has checked everything asserted so far.
			return mAbstraction.isFinal(state);
		}
		if (!statesOf(mSystem.getSourceStates(mWitness.getPc(step))).contains(state)) {
			return false;
		}
		return extend(new Step(step, state), state, 0);
	}

	/**
	 * Depth-first search for the letter path of one pc step.
	 *
	 * @param length
	 *            how many letters of this step have been taken.
	 */
	private boolean extend(final Step step, final STATE current, final int length) {
		pollCancellation();

		// Can this step end here? A zero-length step is legitimate: an edge whose path expression is Epsilon
		// composes to the trivial transition formula.
		if (canEndStep(step, current) && endStep(step, current)) {
			return true;
		}

		// A path that has come back to its own start is complete by construction and must not run on.
		if (mStack.isEmpty() && current.equals(step.mFirst) && length > 0) {
			return false;
		}

		final List<Alternative> alternatives = alternatives(step, current);
		// Only where the run branches does the solver have to say whether a symbolic letter can be taken; a single
		// way on is taken anyway, and a contradiction surfaces at the next check.
		final boolean branching = alternatives.size() > 1;
		for (final Alternative alternative : alternatives) {
			if (tryAlternative(step, alternative, length, branching)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Every way the run can go on from {@code current}: the concrete ones of all useful transitions first, then the
	 * symbolic ones, which are built only when they are tried.
	 */
	private List<Alternative> alternatives(final Step step, final STATE current) {
		mPool.mStep = step;
		final List<Alternative> concrete = new ArrayList<>();
		final List<Alternative> symbolic = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(current)) {
			final Move move = move(step, out.getLetter(), out.getSucc(), Kind.INTERNAL, null);
			if (move != null) {
				execute(step, move, out.getLetter().getTransformula(), StepKind.INTERNAL, concrete, symbolic);
			}
		}
		for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(current)) {
			final Move move = move(step, call.getLetter(), call.getSucc(), Kind.CALL, current);
			if (move != null) {
				execute(step, move, asCallAction(call.getLetter()).getLocalVarsAssignment(), StepKind.CALL_OR_RETURN,
						concrete, symbolic);
			}
		}
		if (!mStack.isEmpty()) {
			final Frame frame = mStack.peek();
			for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction.returnSuccessorsGivenHier(current,
					frame.mCallSite)) {
				final Move move = move(step, ret.getLetter(), ret.getSucc(), Kind.RETURN, null);
				if (move != null) {
					execute(step, move, asReturnAction(ret.getLetter()).getAssignmentOfReturn(),
							StepKind.CALL_OR_RETURN, concrete, symbolic);
				}
			}
		}
		concrete.addAll(symbolic);
		return concrete;
	}

	/**
	 * A transition the search could take next, or {@code null} if it is pruned: because no target of the step is
	 * reachable behind it, because this step's path has already been here with the same calls open, or because the
	 * step has opened as many calls as it can.
	 *
	 * @param entered
	 *            the state the call is made in, if the letter is a call
	 */
	private Move move(final Step step, final LETTER letter, final STATE succ, final Kind kind, final STATE entered) {
		if (!step.mUseful.contains(succ) || kind == Kind.CALL && mStack.size() >= step.mMaxOpenCalls) {
			return null;
		}
		final Object node = nodeAfter(succ, entered, kind == Kind.RETURN);
		if (step.mVisited.contains(node) && !succ.equals(step.mFirst)) {
			return null;
		}
		return new Move(letter, succ, kind, node);
	}

	/**
	 * Executes the formula {@code tf} of {@code move} on the run's values: adds an alternative per successor the
	 * interpreter finds to {@code concrete}, and the symbolic alternative to {@code symbolic} unless the successors
	 * are known to be all there are.
	 */
	private void execute(final Step step, final Move move, final UnmodifiableTransFormula tf, final StepKind kind,
			final List<Alternative> concrete, final List<Alternative> symbolic) {
		mPool.mSuccessor = move.mSucc;
		final Set<TermVariable> free = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		final Map<IProgramVarOrConst, IConcreteValue> pre = new HashMap<>(mConstantValues);
		boolean readsUnknown = false;
		boolean executable = true;
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			if (!free.contains(in.getValue())) {
				continue;
			}
			final IProgramVar pv = in.getKey();
			final Slot slot = mCurrent.get(pv);
			if (slot instanceof final Known known && known.mValue != null) {
				pre.put(pv, known.mValue);
			} else if (slot == null && !pv.isOldvar() && !readCandidates(step.mIndex, pv).isEmpty()) {
				// Left open, so that the interpreter chooses it. It has to be the interpreter: only it can build an
				// array from the cells the letter fixes, and only it can drop a choice before all others are made.
				readsUnknown = true;
			} else {
				// A constant of the solver, a literal the interpreter cannot read, an oldvar that only the default
				// constant stands for, or a variable of a sort the interpreter has no values of: only the solver can
				// go on.
				executable = false;
			}
		}
		boolean exhaustive = executable && !readsUnknown;
		if (executable) {
			exhaustive &= executeLetter(move, tf, kind, pre, concrete);
		}
		if (!exhaustive) {
			symbolic.add(new Alternative(move, true));
		}
	}

	/**
	 * Executes {@code tf}, adding an alternative per execution to {@code concrete}.
	 *
	 * @return whether the executions are all there are
	 */
	private boolean executeLetter(final Move move, final UnmodifiableTransFormula tf, final StepKind kind,
			final Map<IProgramVarOrConst, IConcreteValue> pre, final List<Alternative> concrete) {
		final Execution execution = mExecutor.executeDetailed(tf, pre, pre, kind);
		for (final Successor successor : execution.successors()) {
			final Map<IProgramVarOrConst, IConcreteValue> post = successor.valuation();
			final Alternative alternative = new Alternative(move, false);
			successor.chosenReads().forEach(
					(pv, value) -> alternative.mReads.put(pv, new Known(value, pv.getTermVariable().getSort())));
			final Map<IProgramVar, Slot> written = new LinkedHashMap<>();
			if (kind == StepKind.INTERNAL) {
				for (final IProgramVar pv : tf.getInVars().keySet()) {
					if (!pv.isOldvar() && !tf.getOutVars().containsKey(pv)) {
						// Havoced: no value until it is read again.
						written.put(pv, null);
					}
				}
			}
			for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
				final IProgramVar pv = out.getKey();
				if (out.getValue() == tf.getInVars().get(pv)) {
					continue;
				}
				if (pv.isOldvar()) {
					throw oldVarAssigned(tf, pv);
				}
				final IConcreteValue value = post.get(pv);
				written.put(pv, value == null ? null : new Known(value, pv.getTermVariable().getSort()));
			}
			completeEffect(alternative, written);
			concrete.add(alternative);
		}
		return execution.exhaustive();
	}

	/**
	 * Fills in what taking the alternative's move does besides writing {@code written}, the variables the letter's own
	 * formula assigns: at a call, the oldvars and the callee's locals; at a return, the restoring of the caller's
	 * view.
	 */
	private void completeEffect(final Alternative alternative, final Map<IProgramVar, Slot> written) {
		final Move move = alternative.mMove;
		switch (move.mKind) {
		case INTERNAL:
			alternative.mUpdates.putAll(written);
			break;
		case CALL: {
			alternative.mUpdates.putAll(written);
			final String callee = move.mLetter.getSucceedingProcedure();
			final UnmodifiableTransFormula oldVarsAssignment =
					mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
			for (final IProgramVar assigned : oldVarsAssignment.getAssignedVars()) {
				if (!(assigned instanceof IProgramOldVar)) {
					throw new KInductionCounterexampleException("the oldvar assignment of " + callee + " assigns "
							+ assigned + ", which is not an old variable");
				}
				final IProgramVar global = ((IProgramOldVar) assigned).getNonOldVar();
				Slot value = alternative.mReads.containsKey(global) ? alternative.mReads.get(global)
						: mCurrent.get(global);
				if (value == null && oldVarsRead().contains(assigned)) {
					// old(g) and g are the same value at the entry, which neither may lose when it is chosen later.
					// A constant ties them together. Where no letter reads old(g), there is nothing to tie, and g
					// stays open: a constant here would make everything that reads g symbolic.
					value = new Symbolic(nextConstant(global));
					alternative.mReads.put(global, value);
				}
				alternative.mUpdates.put(assigned, value);
			}
			// Everything of the callee the call did not give a value to starts the activation without one. What the
			// call did give a value to is what the formula writes - deliberately not
			// localVarsAssignment.getAssignedVars(), which also reports a variable that the formula only *reads*
			// without an outvar (computeAssignedVars counts that as havoced). For a call between two procedures the
			// difference is invisible, because the caller's variables are not locals of the callee. For a recursive
			// call they are the very same IProgramVars: the actual parameter's variable would then be taken for one the
			// call assigns, so it would never lose its value here, never end up in the frame, and never be restored
			// when the activation returns - leaving the caller reading the callee's value.
			for (final ILocalProgramVar local : mCsToolkit.getSymbolTable().getLocals(callee)) {
				if (!alternative.mUpdates.containsKey(local)) {
					alternative.mUpdates.put(local, null);
				}
			}
			break;
		}
		case RETURN:
			// The callee's variables go out of scope with the return, after its outparams were read. What the return
			// itself assigns belongs to the caller and has to survive that: in a recursive call the caller's receiving
			// variable and the callee's local are the same IProgramVar, so restoring the scope on top of the
			// assignment would throw the returned value away and leave the caller with its own pre-call value.
			alternative.mUpdates.putAll(mStack.peek().mCalleeScope);
			alternative.mUpdates.putAll(written);
			break;
		default:
			throw new AssertionError("unknown kind " + move.mKind);
		}
	}

	/**
	 * Builds the symbolic alternative of {@code move} for the run as it is now: the formula over the run's slots, with
	 * a fresh constant for every variable it writes and for every one it reads that has no value. Built just before
	 * the alternative is tried, outside the scope it is asserted in: building declares constants, and a declaration
	 * made inside a scope is forgotten when that scope is popped while the cache would happily hand the stale term out
	 * again.
	 */
	private void buildSymbolic(final Alternative alternative) {
		final Move move = alternative.mMove;
		final Map<IProgramVar, Slot> written = new LinkedHashMap<>();
		switch (move.mKind) {
		case INTERNAL:
			alternative.mAssertion =
					ssaOfTransFormula(move.mLetter.getTransformula(), written, alternative.mReads, true);
			break;
		case CALL:
			alternative.mAssertion = ssaOfTransFormula(asCallAction(move.mLetter).getLocalVarsAssignment(), written,
					alternative.mReads, false);
			break;
		case RETURN:
			alternative.mAssertion = ssaOfTransFormula(asReturnAction(move.mLetter).getAssignmentOfReturn(), written,
					alternative.mReads, false);
			break;
		default:
			throw new AssertionError("unknown kind " + move.mKind);
		}
		completeEffect(alternative, written);
	}

	/**
	 * Takes one alternative and continues the search behind it. A symbolic one is asserted, and where the run branches
	 * the solver must still find the run feasible. Everything it changed - the run, the slots, the call stack and the
	 * solver scope - is undone if the search comes back.
	 */
	private boolean tryAlternative(final Step step, final Alternative alternative, final int length,
			final boolean branching) {
		if (alternative.mSymbolic) {
			buildSymbolic(alternative);
		}
		final Move move = alternative.mMove;
		final boolean uncheckedBefore = mUnchecked;
		boolean pushed = false;
		if (alternative.mAssertion != null) {
			push();
			pushed = true;
			mMgdScript.assertTerm(mLockOwner, alternative.mAssertion);
			if (branching) {
				if (checkSat() == LBool.UNSAT) {
					pop();
					return false;
				}
				mUnchecked = false;
			} else {
				mUnchecked = true;
			}
		}
		// Reads first: an update of the same variable has to win.
		final Map<IProgramVar, Slot> undoReads = applyUpdates(alternative.mReads);
		final Map<IProgramVar, Slot> undo = applyUpdates(alternative.mUpdates);
		if (mLetters.size() + 1 > mFurthestLetters) {
			mFurthestLetters = mLetters.size() + 1;
			mFurthestLetterState = move.mSucc;
			mFurthestLetterStep = step.mIndex;
		}
		final int position = mLetters.size();
		mLetters.add(move.mLetter);
		mStates.add(move.mSucc);
		mTakenSymbolically.add(alternative.mSymbolic);
		Frame returned = null;
		switch (move.mKind) {
		case CALL:
			// The frame remembers the caller's view of everything the call overwrote, which is what its return
			// puts back.
			mNesting.add(NestedWord.PLUS_INFINITY);
			mStack.push(new Frame(mStates.get(position), position, undo));
			break;
		case RETURN:
			returned = mStack.pop();
			mNesting.add(returned.mCallPosition);
			// The call is no longer pending: it is matched by this return.
			mNesting.set(returned.mCallPosition, position);
			break;
		default:
			mNesting.add(NestedWord.INTERNAL_POSITION);
		}
		// The successor may be the state the step started in, which is already visited; do not drop it again
		// on backtracking.
		final boolean newlyVisited = step.mVisited.add(move.mNode);
		if (extend(step, move.mSucc, length + 1)) {
			return true;
		}
		if (newlyVisited) {
			step.mVisited.remove(move.mNode);
		}
		if (move.mKind == Kind.CALL) {
			mStack.pop();
		} else if (returned != null) {
			mNesting.set(returned.mCallPosition, NestedWord.PLUS_INFINITY);
			mStack.push(returned);
		}
		mNesting.remove(mNesting.size() - 1);
		mTakenSymbolically.remove(mTakenSymbolically.size() - 1);
		mStates.remove(mStates.size() - 1);
		mLetters.remove(mLetters.size() - 1);
		applyUpdates(undo);
		applyUpdates(undoReads);
		if (pushed) {
			pop();
		}
		mUnchecked = uncheckedBefore;
		return false;
	}

	/**
	 * Ends the current pc step at {@code current}, which is a target of it: the run must have the pins of the next
	 * state there. A variable without a value takes its pin, a constant of the solver is asserted to equal it, and a
	 * value has to be it. Then, if the state is one to commit to (see the class javadoc), every constant still open
	 * gets the value of the solver's model, and the search goes on with the next step.
	 */
	private boolean endStep(final Step step, final STATE current) {
		final int boundary = step.mIndex + 1;
		final Map<IProgramVar, Slot> adopted = new LinkedHashMap<>();
		final List<Term> equalities = new ArrayList<>();
		for (final Map.Entry<IProgramVar, Term> pin : mWitness.getPins(boundary).entrySet()) {
			final IProgramVar pv = pin.getKey();
			final Slot slot = mCurrent.get(pv);
			if (slot == null) {
				adopted.put(pv, known(pin.getValue()));
				continue;
			}
			if (slot instanceof final Known known) {
				final IConcreteValue pinValue = valueOf(pin.getValue());
				if (known.mValue != null && pinValue != null) {
					if (!known.mValue.equals(pinValue)) {
						pinMismatch(step, pv + " is " + known.mValue + " but the model says " + pinValue);
						return false;
					}
					continue;
				}
				if (known.term(script()) == pin.getValue()) {
					continue;
				}
			}
			equalities.add(SmtUtils.binaryEquality(script(), slot.term(script()), pin.getValue()));
		}
		final boolean commit = isCommitPoint(boundary);
		final boolean uncheckedBefore = mUnchecked;
		boolean pushed = false;
		if (!equalities.isEmpty() || mUnchecked || commit && hasSymbolicSlot()) {
			push();
			pushed = true;
			for (final Term equality : equalities) {
				mMgdScript.assertTerm(mLockOwner, equality);
			}
			if (checkSat() == LBool.UNSAT) {
				pop();
				pinMismatch(step, "the solver finds no values that reach the pins " + mWitness.getPins(boundary));
				return false;
			}
			mUnchecked = false;
		}
		final Map<IProgramVar, Slot> undoAdopted = applyUpdates(adopted);
		final List<Runnable> undoCommit = commit && pushed ? commit() : List.of();
		if (solveFrom(boundary, current)) {
			return true;
		}
		for (int i = undoCommit.size() - 1; i >= 0; i--) {
			undoCommit.get(i).run();
		}
		applyUpdates(undoAdopted);
		if (pushed) {
			pop();
		}
		mUnchecked = uncheckedBefore;
		return false;
	}

	/** Whether the run may be committed to the pins of state {@code boundary}, see the class javadoc. */
	private boolean isCommitPoint(final int boundary) {
		return !mWitness.knowsOpenActivations() && mWitness.isFullyPinned(boundary);
	}

	private boolean hasSymbolicSlot() {
		if (mCurrent.values().stream().anyMatch(Symbolic.class::isInstance)) {
			return true;
		}
		for (final Frame frame : mStack) {
			if (frame.mCalleeScope.values().stream().anyMatch(Symbolic.class::isInstance)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Gives every constant of the run the value of the solver's model, which must have been computed by the last
	 * check-sat. The next step then starts concrete.
	 *
	 * @return what undoes it, in the order it was done
	 */
	private List<Runnable> commit() {
		final List<Map<IProgramVar, Slot>> scopes = new ArrayList<>();
		scopes.add(mCurrent);
		for (final Frame frame : mStack) {
			scopes.add(frame.mCalleeScope);
		}
		final Set<Term> constants = new LinkedHashSet<>();
		for (final Map<IProgramVar, Slot> scope : scopes) {
			for (final Slot slot : scope.values()) {
				// Only the sorts a solver reports literals of, see KInductionWitness; the rest stays open.
				if (slot instanceof final Symbolic symbolic
						&& SmtUtils.isSortForWhichWeCanGetValues(symbolic.constant().getSort())) {
					constants.add(symbolic.constant());
				}
			}
		}
		if (constants.isEmpty()) {
			return List.of();
		}
		final Map<Term, Term> model = SmtUtils.getValues(script(), constants);
		final List<Runnable> undo = new ArrayList<>();
		for (final Map<IProgramVar, Slot> scope : scopes) {
			for (final Map.Entry<IProgramVar, Slot> entry : new ArrayList<>(scope.entrySet())) {
				if (entry.getValue() instanceof final Symbolic symbolic && model.containsKey(symbolic.constant())) {
					final Term value = model.get(symbolic.constant());
					if (value == null || value.getFreeVars().length > 0) {
						continue;
					}
					final IProgramVar pv = entry.getKey();
					scope.put(pv, known(value));
					// By key, not by entry: the search in between may have removed and re-added it.
					undo.add(() -> scope.put(pv, symbolic));
				}
			}
		}
		mCommits++;
		return undo;
	}

	private void pinMismatch(final Step step, final String why) {
		if (step.mIndex >= mDeepestPinMismatchStep) {
			mDeepestPinMismatchStep = step.mIndex;
			mDeepestPinMismatch = why;
		}
	}

	/**
	 * Where a pc step may end: at a target node of the step whose state is {@code current} and whose call site chain
	 * is exactly the calls this search still has open.
	 * <p>
	 * For a node of the entry procedure that chain is empty, i.e. no call may be left open - the summary of a
	 * call-to-return span is one edge, so a step never ends in the middle of a summarized call. For a node of an
	 * <b>unfolded</b> callee it is the call sites the copy was made for, and the search has walked exactly those
	 * calls to get here, so ending a step inside a callee is not only allowed but expected: its loop heads are pc
	 * values of their own.
	 * <p>
	 * The one node whose chain says less than the stack is an error imported from a <em>summarized</em> callee: it
	 * names only the call site of the direct call, while the error may lie several summarized levels deeper. Such
	 * a node keeps the older, weaker rule - any open calls, and nothing may follow.
	 */
	private boolean canEndStep(final Step step, final STATE current) {
		for (final CallNode<STATE> target : step.mTargets) {
			if (!target.getState().equals(current)) {
				continue;
			}
			if (mSummarizedErrorTargets.contains(target)) {
				if (step.mIndex + 1 == mSteps) {
					return true;
				}
			} else if (openCallsMatch(target.getCallSites(), step.mIndex + 1)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Whether the calls the search has open fit {@code callSites}, the chain of call sites the node was reached
	 * through, innermost first.
	 * <p>
	 * Without recursion the chain is the whole story: a node of an unfolded copy exists once per chain, so the open
	 * calls have to be exactly it. A stack-encoded procedure's states occur once however deep the recursion goes, so
	 * its nodes carry no chain at all, and a node of an unfolded copy inside one carries only the part of the chain
	 * the graph still distinguishes. There the chain is an innermost prefix of the open calls and the rest are the
	 * activations {@link CallStack} keeps in the state instead of in the graph - which is exactly the information
	 * the node cannot carry. How many those are is not guesswork either: the witness read the stack pointer off the
	 * model, so the test stays exact, which matters because the search is a backtracking one and an open-ended
	 * depth would make it explore every depth at every step boundary.
	 */
	private boolean openCallsMatch(final List<STATE> callSites, final int boundary) {
		// A call into a stack-encoded procedure is the only kind that moves the stack pointer, so the calls open at
		// a node are exactly its chain plus the activations the stack is holding at this point of the run.
		final int expected =
				callSites.size() + (mWitness.knowsOpenActivations() ? mWitness.getOpenActivations(boundary) : 0);
		if (mStack.size() != expected) {
			return false;
		}
		int i = 0;
		// An ArrayDeque used as a stack iterates from its top, so the innermost call comes first, as in the chain.
		for (final Frame frame : mStack) {
			if (i == callSites.size()) {
				return true;
			}
			if (!frame.mCallSite.equals(callSites.get(i++))) {
				return false;
			}
		}
		return true;
	}

	private Set<STATE> statesOf(final Collection<CallNode<STATE>> nodes) {
		final Set<STATE> result = new LinkedHashSet<>();
		for (final CallNode<STATE> node : nodes) {
			result.add(node.getState());
		}
		return result;
	}

	/**
	 * The search node a letter leads to: the state together with the call sites that are open once the letter has
	 * been taken. That is what "already visited on this step's path" has to mean, because the same state inside
	 * and outside a call differ in what the run may do next.
	 *
	 * @param entered
	 *            the call site, if the letter is a call
	 * @param leavesCall
	 *            whether the letter is a return
	 */
	private Object nodeAfter(final STATE state, final STATE entered, final boolean leavesCall) {
		final List<STATE> context = new ArrayList<>(mStack.size() + 1);
		for (final Frame frame : mStack) {
			// An ArrayDeque used as a stack iterates from its top, so the innermost call comes first.
			context.add(frame.mCallSite);
		}
		if (entered != null) {
			context.add(0, entered);
		} else if (leavesCall) {
			context.remove(0);
		}
		return context.isEmpty() ? state : new Pair<>(state, context);
	}

	/**
	 * Applies {@code updates} to the run, a {@code null} slot meaning "the variable has no value". Returns what the
	 * entries were before, so that the same method undoes it.
	 */
	private Map<IProgramVar, Slot> applyUpdates(final Map<IProgramVar, Slot> updates) {
		final Map<IProgramVar, Slot> previous = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, Slot> entry : updates.entrySet()) {
			previous.put(entry.getKey(), mCurrent.get(entry.getKey()));
			if (entry.getValue() == null) {
				mCurrent.remove(entry.getKey());
			} else {
				mCurrent.put(entry.getKey(), entry.getValue());
			}
		}
		return previous;
	}

	/**
	 * A transition formula over the run's slots, as in a step of {@code PcTransitionSystem}: a variable is read at
	 * its value or constant and written to a fresh constant.
	 *
	 * @param written
	 *            filled with the new slot of every variable the formula assigns. Not applied here - the formula reads
	 *            the old values, and the caller applies the updates once it has the term.
	 * @param reads
	 *            filled with a fresh constant for every variable the formula reads that has no value
	 * @param inOnlyIsHavoc
	 *            whether a variable that is only an inVar is havoced, as in an internal formula. Not so for the
	 *            formulas of a call or a return, whose inVars and outVars belong to different procedures: there
	 *            such a variable is only read.
	 */
	private Term ssaOfTransFormula(final UnmodifiableTransFormula tf, final Map<IProgramVar, Slot> written,
			final Map<IProgramVar, Slot> reads, final boolean inOnlyIsHavoc) {
		final Set<TermVariable> free = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			final IProgramVar pv = in.getKey();
			if (free.contains(in.getValue())) {
				substitution.put(in.getValue(), read(pv, reads));
			}
			if (inOnlyIsHavoc && !pv.isOldvar() && !tf.getOutVars().containsKey(pv)) {
				written.put(pv, null);
			}
		}
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			final IProgramVar pv = out.getKey();
			if (tf.getInVars().get(pv) == out.getValue()) {
				continue;
			}
			if (pv.isOldvar()) {
				throw oldVarAssigned(tf, pv);
			}
			final Term next = nextConstant(pv);
			substitution.put(out.getValue(), next);
			written.put(pv, new Symbolic(next));
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			// Fresh per occurrence, not per letter: the same letter can appear twice in one run.
			substitution.put(aux, PredicateUtils.getIndexedConstant("kicexaux_" + aux.getName(), aux.getSort(),
					mAuxCounter++, mCexConstants, script()));
		}
		return PureSubstitution.apply(mMgdScript, substitution, tf.getFormula());
	}

	/**
	 * The term {@code pv} is read as: its value or its constant. An oldvar that no call on the stack assigned is read
	 * as its default constant, which is what the k-induction encoding does with oldvars outside a call; any other
	 * variable without a value gets a fresh constant, recorded in {@code reads}.
	 */
	private Term read(final IProgramVar pv, final Map<IProgramVar, Slot> reads) {
		final Slot slot = reads.containsKey(pv) ? reads.get(pv) : mCurrent.get(pv);
		if (slot != null) {
			return slot.term(script());
		}
		if (pv.isOldvar()) {
			return pv.getDefaultConstant();
		}
		final Symbolic fresh = new Symbolic(nextConstant(pv));
		reads.put(pv, fresh);
		return fresh.constant();
	}

	/**
	 * A fresh constant for {@code pv}. The prefix and the cache are deliberately separate from the ones
	 * {@link KInduction} uses for its own unrolling, so the two can never alias.
	 */
	private Term nextConstant(final IProgramVar pv) {
		return PredicateUtils.getIndexedConstant("kicex_" + pv.getGloballyUniqueId(),
				pv.getTermVariable().getSort(), mSsaCounter++, mCexConstants, script());
	}

	/** The interpreter's value of a literal of the model, {@code null} if it cannot read it. */
	private IConcreteValue valueOf(final Term literal) {
		return mValueOfLiteral.computeIfAbsent(literal, t -> Optional.ofNullable(IConcreteValue.fromModelTerm(t)))
				.orElse(null);
	}

	/**
	 * The values to try for a variable read without a value: the model's candidates first, then the fixed values of
	 * the value analysis - e.g. for an array, of which the model has none. Empty if the interpreter has no values of
	 * the variable's sort.
	 */
	private List<IConcreteValue> readCandidates(final int step, final IProgramVar pv) {
		final Set<IConcreteValue> result = new LinkedHashSet<>(candidateValues(step, pv));
		try {
			result.addAll(mPool.candidates(pv.getTermVariable().getSort()));
		} catch (final UnsupportedTermException e) {
			// e.g. floating point: the model's candidates or the solver
		}
		return new ArrayList<>(result);
	}

	/**
	 * The values of the model's candidates for {@code pv} in step {@code step} that the interpreter can read: the
	 * variable's own first, then every other value of its sort the step has. The latter is what finds a value that
	 * composing moved to another variable, e.g. an input that is passed on as an argument and then dies.
	 */
	private List<IConcreteValue> candidateValues(final int step, final IProgramVar pv) {
		return mCandidateValues.computeIfAbsent(new Pair<>(step, pv), key -> {
			final Set<IConcreteValue> result = new LinkedHashSet<>();
			addValues(mWitness.getCandidates(step).get(pv), result);
			addValues(mWitness.getStepValues(step).get(pv.getTermVariable().getSort()), result);
			return List.copyOf(result);
		});
	}

	/** {@link #candidateValues} with the pin of the variable at the end of the step, if it has a usable one, first. */
	private List<IConcreteValue> pinFirstCandidates(final int step, final IProgramVar pv) {
		return mPinFirstCandidates.computeIfAbsent(new Pair<>(step, pv), key -> {
			final Set<IConcreteValue> result = new LinkedHashSet<>();
			final Term pin = mWitness.getPins(step + 1).get(pv);
			if (pin != null && valueOf(pin) != null) {
				result.add(valueOf(pin));
			}
			result.addAll(candidateValues(step, pv));
			return List.copyOf(result);
		});
	}

	/**
	 * What {@code step} can still write from {@code state} on: everything assigned behind it, up to the states the
	 * step ends at. A call is followed into the callee, so what the callee writes is included.
	 */
	private Set<IProgramVar> writtenFrom(final Step step, final STATE state) {
		final int targetPc = mWitness.getPc(step.mIndex + 1);
		return mWrittenFrom.computeIfAbsent(new Pair<>(targetPc, state), key -> {
			final Set<STATE> targets = statesOf(step.mTargets);
			final Set<IProgramVar> written = new HashSet<>();
			final Set<STATE> visited = new HashSet<>(Set.of(state));
			final Deque<STATE> worklist = new ArrayDeque<>();
			if (!targets.contains(state)) {
				worklist.add(state);
			}
			while (!worklist.isEmpty()) {
				final STATE current = worklist.poll();
				final List<Pair<UnmodifiableTransFormula, STATE>> outgoing = new ArrayList<>();
				for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(current)) {
					outgoing.add(new Pair<>(out.getLetter().getTransformula(), out.getSucc()));
				}
				for (final OutgoingCallTransition<LETTER, STATE> out : mAbstraction.callSuccessors(current)) {
					outgoing.add(new Pair<>(asCallAction(out.getLetter()).getLocalVarsAssignment(), out.getSucc()));
				}
				for (final OutgoingReturnTransition<LETTER, STATE> out : mAbstraction.returnSuccessors(current)) {
					outgoing.add(new Pair<>(asReturnAction(out.getLetter()).getAssignmentOfReturn(), out.getSucc()));
				}
				for (final Pair<UnmodifiableTransFormula, STATE> out : outgoing) {
					if (step.mUseful.contains(out.getSecond())) {
						written.addAll(out.getFirst().getAssignedVars());
						if (visited.add(out.getSecond()) && !targets.contains(out.getSecond())) {
							worklist.add(out.getSecond());
						}
					}
				}
			}
			return written;
		});
	}

	private void addValues(final List<Term> literals, final Set<IConcreteValue> result) {
		if (literals == null) {
			return;
		}
		for (final Term literal : literals) {
			final IConcreteValue value = valueOf(literal);
			if (value != null) {
				result.add(value);
			}
		}
	}

	private static KInductionCounterexampleException oldVarAssigned(final UnmodifiableTransFormula tf,
			final IProgramVar pv) {
		return new KInductionCounterexampleException("the transition formula " + tf + " assigns the old variable "
				+ pv + ". Only the oldvar assignment of a call does that, which this class applies itself rather than "
				+ "as a letter.");
	}

	private ICallAction asCallAction(final LETTER letter) {
		if (!(letter instanceof ICallAction)) {
			throw new KInductionCounterexampleException("the call letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an ICallAction, so its parameter assignment is "
					+ "unknown");
		}
		return (ICallAction) letter;
	}

	private IReturnAction asReturnAction(final LETTER letter) {
		if (!(letter instanceof IReturnAction)) {
			throw new KInductionCounterexampleException("the return letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an IReturnAction, so its assignment of the return "
					+ "value is unknown");
		}
		return (IReturnAction) letter;
	}

	/**
	 * Turns a failed search into the most specific explanation available.
	 */
	private KInductionCounterexampleException noRunFound(final String what) {
		return new KInductionCounterexampleException(what + ". The search got as far as the start of pc step "
				+ mDeepestStep + " of " + mSteps + ", in state " + mDeepestState + " with " + mDeepestOpenCalls
				+ " call(s) open, and found no letter path for " + (mDeepestStep >= 0 && mDeepestStep < mSteps
						? "the step from pc " + mWitness.getPc(mDeepestStep) + " to pc "
								+ mWitness.getPc(mDeepestStep + 1)
						: "the accepting state it has to end in")
				+ ", whose source(s) are " + (mDeepestStep >= 0 && mDeepestStep < mSteps
						? statesOf(mSystem.getSourceStates(mWitness.getPc(mDeepestStep))).toString()
						: "none")
				+ " and whose target(s) are " + describeTargets() + ". From there the abstraction offers "
				+ describeSuccessors()
				+ ". The longest letter path it ever got was " + mFurthestLetters
				+ " letter(s) long, ending in " + mFurthestLetterState + " during pc step " + mFurthestLetterStep
				+ (mDeepestPinMismatch == null ? ""
						: ". The deepest step that reached a target, step " + mDeepestPinMismatchStep
								+ ", missed the model's values there: " + mDeepestPinMismatch)
				+ ". The pc transition system claims a path that the letters of the abstraction do not admit, "
				+ "which means the two disagree.");
	}

	/**
	 * What the abstraction lets the failed search do next. Without this, "no letter path" leaves open whether the
	 * step could not start at all or died somewhere along the way.
	 */
	private String describeSuccessors() {
		if (mDeepestState == null) {
			return "nothing";
		}
		final Set<STATE> useful = mDeepestStep < mSteps ? canReachATargetOf(mWitness.getPc(mDeepestStep + 1)) : Set.of();
		final StringBuilder sb = new StringBuilder();
		int shown = 0;
		for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(mDeepestState)) {
			shown = append(sb, shown,
					"-" + out.getLetter() + "-> " + out.getSucc() + usefulness(useful, out.getSucc()));
		}
		for (final OutgoingCallTransition<LETTER, STATE> out : mAbstraction.callSuccessors(mDeepestState)) {
			shown = append(sb, shown,
					"-call " + out.getLetter() + "-> " + out.getSucc() + usefulness(useful, out.getSucc()));
		}
		for (final OutgoingReturnTransition<LETTER, STATE> out : mAbstraction.returnSuccessors(mDeepestState)) {
			shown = append(sb, shown, "-return " + out.getLetter() + " over " + out.getHierPred() + "-> "
					+ out.getSucc() + usefulness(useful, out.getSucc()));
		}
		return shown == 0 ? "nothing" : sb.toString();
	}

	/** Whether the search would even try a successor, i.e. whether a target is still reachable behind it. */
	private String usefulness(final Set<STATE> useful, final STATE succ) {
		return useful.contains(succ) ? "" : " [PRUNED: no target of this step is reachable from it]";
	}

	private static int append(final StringBuilder sb, final int shown, final String what) {
		if (shown == MAX_SUCCESSORS_IN_MESSAGE) {
			sb.append(", ...");
		}
		if (shown >= MAX_SUCCESSORS_IN_MESSAGE) {
			return shown + 1;
		}
		sb.append(shown == 0 ? "" : ", ").append(what);
		return shown + 1;
	}

	/** The target nodes of the step the failed search got stuck on, with what each one demands. */
	private String describeTargets() {
		if (mDeepestStep < 0 || mDeepestStep >= mSteps) {
			return "none";
		}
		final StringBuilder sb = new StringBuilder();
		for (final CallNode<STATE> target : mSystem.getTargetStates(mWitness.getPc(mDeepestStep + 1))) {
			sb.append(sb.length() == 0 ? "" : ", ").append(target.getState());
			if (mSummarizedErrorTargets.contains(target)) {
				sb.append(" (an error imported from a summarized callee)");
			} else {
				sb.append(" (reached through ").append(target.getCallSites());
				if (mWitness.knowsOpenActivations()) {
					sb.append(" plus ").append(mWitness.getOpenActivations(mDeepestStep + 1))
							.append(" activation(s)");
				}
				sb.append(')');
			}
		}
		return sb.toString();
	}

	/**
	 * The states from which some target of the pc value {@code targetPc} is still reachable. Prunes the search away
	 * from parts of the automaton that cannot end this step at all. Call and return transitions count as edges here:
	 * over-approximating reachability only weakens the pruning, it can never rule out a real path.
	 */
	private Set<STATE> canReachATargetOf(final int targetPc) {
		return mCanReachTarget.computeIfAbsent(targetPc, pc -> {
			final Map<STATE, List<STATE>> predecessors = predecessors();
			final Set<STATE> result = new HashSet<>(statesOf(mSystem.getTargetStates(pc)));
			final Deque<STATE> worklist = new ArrayDeque<>(result);
			while (!worklist.isEmpty()) {
				for (final STATE pred : predecessors.getOrDefault(worklist.pop(), List.of())) {
					if (result.add(pred)) {
						worklist.push(pred);
					}
				}
			}
			return result;
		});
	}

	/** The old variables that some letter of the abstraction reads. */
	private Set<IProgramVar> oldVarsRead() {
		if (mOldVarsRead == null) {
			mOldVarsRead = new HashSet<>();
			for (final STATE state : mAbstraction.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(state)) {
					addOldVarsRead(out.getLetter().getTransformula());
				}
				for (final OutgoingCallTransition<LETTER, STATE> out : mAbstraction.callSuccessors(state)) {
					addOldVarsRead(asCallAction(out.getLetter()).getLocalVarsAssignment());
				}
				for (final OutgoingReturnTransition<LETTER, STATE> out : mAbstraction.returnSuccessors(state)) {
					addOldVarsRead(asReturnAction(out.getLetter()).getAssignmentOfReturn());
				}
			}
		}
		return mOldVarsRead;
	}

	private void addOldVarsRead(final UnmodifiableTransFormula tf) {
		final Set<TermVariable> free = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			if (in.getKey().isOldvar() && free.contains(in.getValue())) {
				mOldVarsRead.add(in.getKey());
			}
		}
	}

	private Map<STATE, List<STATE>> predecessors() {
		if (mPredecessors == null) {
			mPredecessors = new HashMap<>();
			for (final STATE state : mAbstraction.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(state)) {
					addPredecessor(out.getSucc(), state);
				}
				for (final OutgoingCallTransition<LETTER, STATE> out : mAbstraction.callSuccessors(state)) {
					addPredecessor(out.getSucc(), state);
				}
				for (final OutgoingReturnTransition<LETTER, STATE> out : mAbstraction.returnSuccessors(state)) {
					addPredecessor(out.getSucc(), state);
				}
			}
		}
		return mPredecessors;
	}

	private void addPredecessor(final STATE successor, final STATE predecessor) {
		mPredecessors.computeIfAbsent(successor, k -> new ArrayList<>()).add(predecessor);
	}

	private void pollCancellation() {
		mExpansions++;
		if (mExpansions % 512 == 0 && !mServices.getProgressMonitorService().continueProcessing()) {
			throw new KInductionCounterexampleException(
					"cancelled while reconstructing a counterexample for " + mWitness);
		}
	}

	@SuppressWarnings("unchecked")
	private NestedRun<LETTER, STATE> assemble() {
		if (mLetters.isEmpty()) {
			throw new KInductionCounterexampleException("the reconstructed counterexample is empty; an initial "
					+ "state of the abstraction is also accepting, which no consumer of a counterexample supports");
		}
		final int[] nestingRelation = new int[mNesting.size()];
		for (int i = 0; i < nestingRelation.length; i++) {
			nestingRelation[i] = mNesting.get(i);
		}
		// LETTER erases to IAction, so the array has to be an IAction[] - an Object[], which NestedWord uses for
		// its own unbounded letter type, fails the cast at runtime.
		final IAction[] letters = new IAction[mLetters.size()];
		for (int i = 0; i < letters.length; i++) {
			letters[i] = mLetters.get(i);
		}
		final NestedWord<LETTER> word = new NestedWord<>((LETTER[]) letters, nestingRelation);
		final NestedRun<LETTER, STATE> run = new NestedRun<>(word, new ArrayList<>(mStates));

		final STATE last = mStates.get(mStates.size() - 1);
		if (!mAbstraction.isFinal(last)) {
			throw new AssertionError("the reconstructed run ends in " + last + ", which is not accepting");
		}
		try {
			if (!new Accepts<>(new AutomataLibraryServices(mServices), mAbstraction, word).getResult()) {
				throw new AssertionError("the abstraction does not accept the reconstructed run " + word);
			}
		} catch (final Exception e) {
			throw new AssertionError("could not check the reconstructed run against the abstraction: " + e, e);
		}
		final long symbolic = mTakenSymbolically.stream().filter(Boolean::booleanValue).count();
		mLogger.info("KInduction: reconstructed a counterexample of %d letter(s), %d of them call(s), after %d "
				+ "expansion(s): %d letter(s) executed, %d taken symbolically, %d check-sat(s), %d commit(s) to the "
				+ "model, %d interpreted step(s) of which %d unsupported", mLetters.size(), countCalls(), mExpansions,
				mLetters.size() - symbolic, symbolic, mCheckSats, mCommits, mExecutor.getSteps(),
				mExecutor.getUnsupportedSteps());
		return run;
	}

	/** How many positions of the reconstructed word are calls, matched or still pending. */
	private int countCalls() {
		int result = 0;
		for (int i = 0; i < mNesting.size(); i++) {
			final int nesting = mNesting.get(i);
			if (nesting == NestedWord.PLUS_INFINITY || nesting > i) {
				result++;
			}
		}
		return result;
	}

	private Script script() {
		return mMgdScript.getScript();
	}
}
