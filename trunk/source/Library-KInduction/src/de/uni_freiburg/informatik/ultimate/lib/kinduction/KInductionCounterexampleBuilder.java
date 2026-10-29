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
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.ProcedureSummaries;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;

/**
 * Turns a {@link KInductionWitness} - what the solver's model of a satisfiable base case said - into a concrete
 * {@link NestedRun} of the abstraction that reaches an accepting state.
 *
 * <h2>Why a search is needed at all</h2>
 *
 * A step of the {@link PcTransitionSystem} is not a single letter. Each of its transitions is one edge of one
 * scope's checkpoint graph, and {@link LoopTreeFormulaBuilder} built that edge by composing whole <em>paths</em> of
 * letters: {@code sequentialComposition} for concatenation, {@code parallelComposition} for the union of
 * alternatives, and, at a call site, a whole call-to-return span ({@link ProcedureSummaries}). The union is built
 * without branch indicators, so the composed formula does not record which alternative a model took, and the
 * letters themselves are gone. The model therefore pins down the program state at every checkpoint, but not the
 * way between two of them; that has to be searched for.
 *
 * <h2>What the search may and may not assume</h2>
 *
 * The model is used for the <b>shape</b> of the violation only: which pc node each unrolled state has, and which
 * transition was taken between two of them. That fixes, for every step, the automaton states the letter path has to
 * run between, which is what makes the search tractable.
 * <p>
 * The model's <b>variable values</b> are deliberately not used. A composed edge relation need not agree with any
 * single concrete path about the value a variable ends up with - where the composition leaves an out-variable
 * unconstrained, the model may pick a value no concrete path produces - so constraining the search with those
 * values makes it fail on perfectly good counterexamples. Feasibility is therefore established by the search
 * itself, which is what actually matters.
 * <p>
 * Every path the search considers is checked against the solver as it is extended, over one continuous SSA that
 * spans all steps, so the run that comes back is feasible as a whole and ends in an accepting state. It is
 * therefore a genuine counterexample no matter what the pc encoding did, and
 * {@code KInductionWorkerThread.reportCounterexample} independently confirms it with the ordinary trace check. If
 * the encoding were ever to over-approximate and report a violation that does not exist, no feasible path would be
 * found and this class would throw rather than invent one.
 *
 * <h2>Calls</h2>
 *
 * A pc transition can be a whole call-to-return span, so the search walks call and return transitions as well, with
 * a stack of the call sites it has entered; a return is only ever taken with the hierarchical predecessor that
 * stack names, which is what makes the reconstructed word properly nested. The SSA mirrors what
 * {@code TransFormulaUtils.sequentialCompositionWithCallAndReturn} did to the formula the model was produced from:
 * at a call the parameter assignment is asserted, every oldvar of a global the callee may modify is set to that
 * global's current value, and every local of the callee that is not an inparam becomes an unconstrained fresh
 * constant (it is arbitrary at procedure entry); at the return the assignment of the result is asserted and the
 * callee's scope - those oldvars and locals - is restored to what the caller saw. An oldvar that no call on the
 * stack assigns keeps {@code getDefaultConstant()}, exactly as {@code PcTransitionSystem.instantiate} uses it.
 * <p>
 * A step ends where the pc transition's target nodes are. Each such node carries the call sites it stands for, so
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
 * {@code INIT(h) -> END(h)} in a loop scope runs from the head back to the head. Restricting the search to simple
 * paths alone would drop exactly those, and restricting it no further keeps the search finite. A state visited
 * inside a call is a different search node from the same state visited outside it, since the two differ in what
 * the run may do next, so "simple" is meant with respect to the call stack.
 * <p>
 * A loop that is entered at several heads also has the steps {@code INIT(h1) -> END(h2)}, whose path runs between
 * two <em>different</em> sealed states and is therefore plainly simple. On such a program the search may leave the
 * transition the model named and come back through a third head, so the run it returns need not be the model's.
 * That is harmless: the path was checked against the solver as it was extended, {@link #assemble} re-checks it with
 * {@code Accepts}, and {@code KInductionWorkerThread.reportCounterexample} re-runs the ordinary trace check - so
 * what comes back is a genuine counterexample either way.
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
	 * Cuts off a search that is not going to finish, so that a pathological abstraction produces a legible failure
	 * instead of hanging. Reaching this is a bug or a program far outside what k-induction is used on.
	 */
	private static final int MAX_EXPANSIONS = 100_000;

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
	/** See {@code ProcedureSummaries#getStackedProcedures()}; empty for a program with no recursion. */
	private final Set<String> mStackedProcedures;

	/** Enough of the stuck state's outgoing transitions to see what went wrong, without flooding the log. */
	private static final int MAX_SUCCESSORS_IN_MESSAGE = 8;

	/** How far the search ever got, for the message of a search that then failed. */
	private int mDeepestStep = -1;
	private STATE mDeepestState;
	private int mDeepestOpenCalls;
	/** The longest letter path the search ever had asserted, i.e. how far it got inside a step. */
	private int mFurthestLetters = -1;
	private STATE mFurthestLetterState;
	private int mFurthestLetterStep = -1;

	/** The number of pc steps to reconstruct: everything after it is the FINAL stutter self loop. */
	private final int mSteps;

	// The run being built. All three are undone on backtracking.
	private final List<LETTER> mLetters = new ArrayList<>();
	private final List<STATE> mStates = new ArrayList<>();
	private final List<Integer> mNesting = new ArrayList<>();

	/** The calls the search has entered and not yet left. */
	private final Deque<Frame> mStack = new ArrayDeque<>();

	// SSA state: the constant that currently holds each variable's value, and the counters behind those constants.
	private final Map<IProgramVar, Term> mCurrent = new HashMap<>();
	/**
	 * The constants {@link #current} made up while the SSA of the letter being considered was built, for variables
	 * that had none yet. They are declared at the depth the search is at, so they must leave {@link #mCurrent} again
	 * when the search backtracks above it; see {@link Candidate#mFreshReads}.
	 */
	private final Map<IProgramVar, Term> mFreshReads = new LinkedHashMap<>();
	private final Map<String, Term> mCexConstants = new HashMap<>();
	private int mSsaCounter;
	private int mAuxCounter;

	private int mExpansions;

	/** How many scopes we have pushed. A successful search returns with its whole stack standing; see build(). */
	private int mPushDepth;

	// state -> states reachable from it, computed lazily per transition id
	private final Map<Integer, Set<STATE>> mCanReachTarget = new HashMap<>();
	private Map<STATE, List<STATE>> mPredecessors;

	/**
	 * One entered call: where it was made, which letter position it is, and the SSA entries it overwrote (the
	 * callee's locals and the oldvars of the globals it may modify), so that the return can put the caller's view
	 * back.
	 */
	private final class Frame {
		private final STATE mCallSite;
		private final int mCallPosition;
		private final Map<IProgramVar, Term> mCalleeScope;

		private Frame(final STATE callSite, final int callPosition, final Map<IProgramVar, Term> calleeScope) {
			mCallSite = callSite;
			mCallPosition = callPosition;
			mCalleeScope = calleeScope;
		}
	}

	/** What stays fixed while the letter path of one pc step is searched for. */
	private final class Step {
		private final int mIndex;
		private final Transition<CallNode<STATE>> mTransition;
		/** The state the step started in; the only state the path may return to, and only as its last. */
		private final STATE mFirst;
		/** The search nodes (state plus open calls) already on this step's path. */
		private final Set<Object> mVisited = new LinkedHashSet<>();
		/** The states from which a target of the transition is still reachable. */
		private final Set<STATE> mUseful;

		private Step(final int index, final Transition<CallNode<STATE>> transition, final STATE first) {
			mIndex = index;
			mTransition = transition;
			mFirst = first;
			mUseful = canReachATargetOf(transition);
			mVisited.add(nodeAfter(first, null, false));
		}
	}

	/** One letter the search could take next, with everything taking it would do to the SSA and the run. */
	private final class Candidate {
		private final LETTER mLetter;
		private final STATE mSucc;
		/** The search node the letter leads to, i.e. the successor plus the calls open after it. */
		private final Object mNode;
		/** Non-null exactly for a call: the hierarchical predecessor its return will need. */
		private final STATE mCallSite;
		private final Map<IProgramVar, Term> mUpdates = new LinkedHashMap<>();
		/**
		 * The first constant of every variable the letter reads without it having one yet. Kept apart from
		 * {@link #mUpdates} because a call's frame restores exactly what the call updated at the return, while a
		 * global first read at the call has to keep its constant after the return.
		 */
		private final Map<IProgramVar, Term> mFreshReads = new LinkedHashMap<>();
		private Term mSsa;
		/**
		 * This position's entry in the nesting relation: {@link NestedWord#INTERNAL_POSITION},
		 * {@link NestedWord#PLUS_INFINITY} for a call (replaced by the return's position once it is matched), or
		 * the position of the matching call for a return.
		 */
		private int mNesting;

		private Candidate(final LETTER letter, final STATE succ, final Object node, final STATE callSite) {
			mLetter = letter;
			mSucc = succ;
			mNode = node;
			mCallSite = callSite;
		}
	}

	public KInductionCounterexampleBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final Object lockOwner, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction,
			final PcTransitionSystem<CallNode<STATE>> system, final KInductionWitness witness,
			final Set<CallNode<STATE>> summarizedErrorTargets, final Set<String> stackedProcedures) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mLockOwner = lockOwner;
		mCsToolkit = csToolkit;
		mAbstraction = abstraction;
		mSystem = system;
		mWitness = witness;
		mSummarizedErrorTargets = summarizedErrorTargets;
		mStackedProcedures = stackedProcedures;
		mSteps = witness.getFirstFinalStep();
	}

	/**
	 * @return a feasible run of the abstraction into an accepting state.
	 * @throws KInductionCounterexampleException
	 *             if the violation cannot be expressed as a run of the abstraction.
	 */
	public NestedRun<LETTER, STATE> build() {
		checkWitnessShape();
		mLogger.info("KInduction: reconstructing a counterexample for %d pc step(s) of %s", mSteps, mWitness);

		push();
		try {
			final Transition<CallNode<STATE>> first = mSystem.getTransition(mWitness.getTransitionId(0));
			for (final STATE start : statesOf(first.getSourceStates())) {
				if (!mAbstraction.isInitial(start)) {
					continue;
				}
				mStates.add(start);
				if (solveFrom(0, start)) {
					return assemble();
				}
				mLetters.clear();
				mStates.clear();
				mNesting.clear();
				mStack.clear();
				mCurrent.clear();
			}
			throw noRunFound("no counterexample run starts in any of the initial states "
					+ statesOf(first.getSourceStates())
					+ " of " + first + ", although k-induction reported a violation at k=" + mWitness.getK()
					+ " (" + mWitness + ")");
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

	/** The parts of the witness this class relies on, checked once so a later failure is not misattributed. */
	private void checkWitnessShape() {
		if (mWitness.getPc(0) != PcTransitionSystem.INIT) {
			throw new AssertionError("the base case asserts pc_0 = INIT, but the model says pc_0 = "
					+ mWitness.getPc(0));
		}
		if (mSteps == 0) {
			throw new AssertionError("the model has pc_0 = FINAL although pc_0 = INIT was asserted");
		}
		for (int j = mSteps; j < mWitness.getK(); j++) {
			if (mWitness.getTransitionId(j) != mSystem.getStutterTransitionId()) {
				throw new AssertionError("FINAL has no outgoing transition but the stutter self loop, yet the "
						+ "model leaves it at step " + j + " via t" + mWitness.getTransitionId(j));
			}
		}
		if (mSteps < mWitness.getK()) {
			mLogger.info("KInduction: the model reaches FINAL after %d of %d step(s); the rest is the stutter self "
					+ "loop and is dropped", mSteps, mWitness.getK());
		}
	}

	/**
	 * Continues the search at the start of pc step {@code step}, with the SSA sitting at that step's boundary.
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
			return mAbstraction.isFinal(state);
		}
		final Transition<CallNode<STATE>> transition = mSystem.getTransition(mWitness.getTransitionId(step));
		if (!statesOf(transition.getSourceStates()).contains(state)) {
			return false;
		}
		return extend(new Step(step, transition, state), state, 0);
	}

	/**
	 * Depth-first search for the letter path of one pc step.
	 *
	 * @param length
	 *            how many letters of this step have been taken.
	 */
	private boolean extend(final Step step, final STATE current, final int length) {
		checkBudget();

		// Can this step end here? A zero-length step is legitimate: an edge whose path expression is Epsilon
		// composes to the trivial transition formula.
		if (canEndStep(step, current) && solveFrom(step.mIndex + 1, current)) {
			return true;
		}

		// A path that has come back to its own start is complete by construction and must not run on.
		if (mStack.isEmpty() && current.equals(step.mFirst) && length > 0) {
			return false;
		}

		for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(current)) {
			final Candidate candidate = candidate(step, out.getLetter(), out.getSucc(), null, false);
			if (candidate == null) {
				continue;
			}
			// Built before the push on purpose: it declares constants, and a declaration made inside a scope is
			// forgotten when that scope is popped while the cache would happily hand the stale term out again.
			candidate.mSsa = ssaOfTransFormula(out.getLetter().getTransformula(), candidate.mUpdates, true);
			takeFreshReads(candidate);
			candidate.mNesting = NestedWord.INTERNAL_POSITION;
			if (tryLetter(step, candidate, length)) {
				return true;
			}
		}
		for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(current)) {
			final Candidate candidate = candidate(step, call.getLetter(), call.getSucc(), current, false);
			if (candidate == null) {
				continue;
			}
			candidate.mSsa = ssaOfCall(asCallAction(call.getLetter()),
					call.getLetter().getSucceedingProcedure(), candidate.mUpdates);
			takeFreshReads(candidate);
			candidate.mNesting = NestedWord.PLUS_INFINITY;
			if (tryLetter(step, candidate, length)) {
				return true;
			}
		}
		if (!mStack.isEmpty()) {
			final Frame frame = mStack.peek();
			for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction.returnSuccessorsGivenHier(current,
					frame.mCallSite)) {
				final Candidate candidate = candidate(step, ret.getLetter(), ret.getSucc(), null, true);
				if (candidate == null) {
					continue;
				}
				final Map<IProgramVar, Term> assignedByReturn = new LinkedHashMap<>();
				candidate.mSsa =
						ssaOfTransFormula(asReturnAction(ret.getLetter()).getAssignmentOfReturn(),
								assignedByReturn, false);
				takeFreshReads(candidate);
				// The callee's variables go out of scope with the return, after its outparams were read above.
				// What the return itself assigns belongs to the caller and has to survive that: in a recursive
				// call the caller's receiving variable and the callee's local are the same IProgramVar, so
				// restoring the scope on top of the assignment would throw the returned value away and leave the
				// caller with its own pre-call value.
				candidate.mUpdates.putAll(frame.mCalleeScope);
				candidate.mUpdates.putAll(assignedByReturn);
				candidate.mNesting = frame.mCallPosition;
				if (tryLetter(step, candidate, length)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * A letter the search could take next, or {@code null} if it is pruned: because no target of the step is
	 * reachable behind it, or because this step's path has already been here with the same calls open.
	 *
	 * @param entered
	 *            the state the call is made in, if the letter is a call
	 * @param leavesCall
	 *            whether the letter is a return
	 */
	private Candidate candidate(final Step step, final LETTER letter, final STATE succ, final STATE entered,
			final boolean leavesCall) {
		if (!step.mUseful.contains(succ)) {
			return null;
		}
		final Object node = nodeAfter(succ, entered, leavesCall);
		if (step.mVisited.contains(node) && !succ.equals(step.mFirst)) {
			return null;
		}
		return new Candidate(letter, succ, node, entered);
	}

	/**
	 * Takes one letter if the solver still finds the run feasible, and continues the search behind it. Everything
	 * it changed - the run, the SSA, the call stack and the solver scope - is undone if the search comes back.
	 */
	private boolean tryLetter(final Step step, final Candidate candidate, final int length) {
		// Reads first: an update of the same variable has to win.
		final Map<IProgramVar, Term> undoReads = applyUpdates(candidate.mFreshReads);
		final Map<IProgramVar, Term> undo = applyUpdates(candidate.mUpdates);
		push();
		mMgdScript.assertTerm(mLockOwner, candidate.mSsa);
		if (mMgdScript.checkSat(mLockOwner) != LBool.UNSAT) {
			if (mLetters.size() + 1 > mFurthestLetters) {
				mFurthestLetters = mLetters.size() + 1;
				mFurthestLetterState = candidate.mSucc;
				mFurthestLetterStep = step.mIndex;
			}
			final int position = mLetters.size();
			mLetters.add(candidate.mLetter);
			mStates.add(candidate.mSucc);
			mNesting.add(candidate.mNesting);
			Frame returned = null;
			if (candidate.mCallSite != null) {
				// The frame remembers the caller's view of everything the call overwrote, which is what its
				// return puts back.
				mStack.push(new Frame(candidate.mCallSite, position, undo));
			} else if (candidate.mNesting != NestedWord.INTERNAL_POSITION) {
				returned = mStack.pop();
				// The call is no longer pending: it is matched by this return.
				mNesting.set(returned.mCallPosition, position);
			}
			// The successor may be the state the step started in, which is already visited; do not drop it again
			// on backtracking.
			final boolean newlyVisited = step.mVisited.add(candidate.mNode);
			if (extend(step, candidate.mSucc, length + 1)) {
				return true;
			}
			if (newlyVisited) {
				step.mVisited.remove(candidate.mNode);
			}
			if (candidate.mCallSite != null) {
				mStack.pop();
			} else if (returned != null) {
				mNesting.set(returned.mCallPosition, NestedWord.PLUS_INFINITY);
				mStack.push(returned);
			}
			mNesting.remove(mNesting.size() - 1);
			mStates.remove(mStates.size() - 1);
			mLetters.remove(mLetters.size() - 1);
		}
		pop();
		applyUpdates(undo);
		applyUpdates(undoReads);
		return false;
	}

	/** Hands the constants {@link #current} made up for the candidate's SSA over to the candidate. */
	private void takeFreshReads(final Candidate candidate) {
		candidate.mFreshReads.putAll(mFreshReads);
		mFreshReads.clear();
	}



	/**
	 * Where a pc step may end: at a target node of the transition whose state is {@code current} and whose call
	 * site chain is exactly the calls this search still has open.
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
		for (final CallNode<STATE> target : step.mTransition.getTargetStates()) {
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
	 * Applies {@code updates} to the SSA, a {@code null} value meaning "the variable has no constant". Returns what
	 * the entries were before, so that the same method undoes it.
	 */
	private Map<IProgramVar, Term> applyUpdates(final Map<IProgramVar, Term> updates) {
		final Map<IProgramVar, Term> previous = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, Term> entry : updates.entrySet()) {
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
	 * A transition formula over the SSA constants, following {@code PcTransitionSystem.instantiate}: a variable is
	 * read at the constant that currently holds it and written to a fresh one.
	 *
	 * @param updates
	 *            filled with the new constant of every variable the formula assigns. Not applied here - the
	 *            formula reads the old values, and the caller applies the updates once it has the term.
	 * @param inOnlyIsHavoc
	 *            whether a variable that is only an inVar is havoced, as in an internal formula. Not so for the
	 *            formulas of a call or a return, whose inVars and outVars belong to different procedures: there
	 *            such a variable is only read.
	 */
	private Term ssaOfTransFormula(final UnmodifiableTransFormula tf, final Map<IProgramVar, Term> updates,
			final boolean inOnlyIsHavoc) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			final IProgramVar pv = in.getKey();
			substitution.put(in.getValue(), current(pv));
			if (inOnlyIsHavoc && !pv.isOldvar() && !tf.getOutVars().containsKey(pv)) {
				updates.put(pv, nextConstant(pv));
			}
		}
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			final IProgramVar pv = out.getKey();
			if (tf.getInVars().get(pv) == out.getValue()) {
				continue;
			}
			if (pv.isOldvar()) {
				throw new KInductionCounterexampleException("the transition formula " + tf + " assigns the old "
						+ "variable " + pv + ". Only the oldvar assignment of a call does that, which this class "
						+ "applies itself rather than as a letter.");
			}
			final Term next = nextConstant(pv);
			substitution.put(out.getValue(), next);
			updates.put(pv, next);
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			// Fresh per occurrence, not per letter: the same letter can appear twice in one run.
			substitution.put(aux, PredicateUtils.getIndexedConstant("kicexaux_" + aux.getName(), aux.getSort(),
					mAuxCounter++, mCexConstants, script()));
		}
		return PureSubstitution.apply(mMgdScript, substitution, tf.getFormula());
	}

	/**
	 * What entering {@code callee} does to the SSA, mirroring the call/oldvars/globals part of
	 * {@code TransFormulaUtils.sequentialCompositionWithCallAndReturn}: the parameter assignment (the returned
	 * term), {@code old(g) := g} for every global the callee may modify, and an arbitrary value for every local of
	 * the callee that the call does not assign.
	 *
	 * @param updates
	 *            filled with all of that; the caller applies it, and the matching return undoes everything but the
	 *            parameter assignment.
	 */
	private Term ssaOfCall(final ICallAction callAction, final String callee,
			final Map<IProgramVar, Term> updates) {
		final UnmodifiableTransFormula localVarsAssignment = callAction.getLocalVarsAssignment();
		final Term result = ssaOfTransFormula(localVarsAssignment, updates, false);
		final UnmodifiableTransFormula oldVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		for (final IProgramVar assigned : oldVarsAssignment.getAssignedVars()) {
			if (!(assigned instanceof IProgramOldVar)) {
				throw new KInductionCounterexampleException("the oldvar assignment of " + callee + " assigns "
						+ assigned + ", which is not an old variable");
			}
			updates.put(assigned, current(((IProgramOldVar) assigned).getNonOldVar()));
		}
		// Everything of the callee the call did not give a value to starts the activation unconstrained. What the
		// call did give a value to is what ssaOfTransFormula just recorded in "updates" - deliberately not
		// localVarsAssignment.getAssignedVars(), which also reports a variable that the formula only *reads*
		// without an outvar (computeAssignedVars counts that as havoced). For a call between two procedures the
		// difference is invisible, because the caller's variables are not locals of the callee. For a recursive
		// call they are the very same IProgramVars: the actual parameter's variable would then be taken for one the
		// call assigns, so it would never be havoced here, never end up in the frame, and never be restored when
		// the activation returns - leaving the caller reading the callee's value.
		for (final ILocalProgramVar local : mCsToolkit.getSymbolTable().getLocals(callee)) {
			if (!updates.containsKey(local)) {
				updates.put(local, nextConstant(local));
			}
		}
		return result;
	}

	/**
	 * The constant that currently holds {@code pv}. An oldvar that no call on the stack assigned has none and uses
	 * its default constant, which is what the k-induction encoding does with oldvars outside a call.
	 */
	private Term current(final IProgramVar pv) {
		final Term existing = mCurrent.get(pv);
		if (existing != null) {
			return existing;
		}
		if (pv.isOldvar()) {
			return pv.getDefaultConstant();
		}
		// Not straight into mCurrent: the constant is declared at the current depth, and tryLetter has to be able to
		// take it out again on backtracking, which it can only for what the candidate carries.
		return mFreshReads.computeIfAbsent(pv, this::nextConstant);
	}

	/**
	 * A fresh constant for {@code pv}. The prefix and the cache are deliberately separate from the ones
	 * {@link KInduction} uses for its own unrolling, so the two can never alias.
	 */
	private Term nextConstant(final IProgramVar pv) {
		return PredicateUtils.getIndexedConstant("kicex_" + pv.getGloballyUniqueId(),
				pv.getTermVariable().getSort(), mSsaCounter++, mCexConstants, script());
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
				+ " call(s) open, and found no letter path for " + (mDeepestStep < mSteps
						? mSystem.getTransition(mWitness.getTransitionId(mDeepestStep)).toString()
						: "the accepting state it has to end in")
				+ ", whose source(s) are " + (mDeepestStep < mSteps
						? statesOf(mSystem.getTransition(mWitness.getTransitionId(mDeepestStep)).getSourceStates())
								.toString()
						: "none")
				+ " and whose target(s) are " + describeTargets() + ". From there the abstraction offers "
				+ describeSuccessors()
				+ ". The longest letter path it ever got the solver to accept was " + mFurthestLetters
				+ " letter(s) long, ending in " + mFurthestLetterState + " during pc step " + mFurthestLetterStep
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
		final Set<STATE> useful = mDeepestStep < mSteps
				? canReachATargetOf(mSystem.getTransition(mWitness.getTransitionId(mDeepestStep)))
				: Set.of();
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
		return useful.contains(succ) ? "" : " [PRUNED: no target of this transition is reachable from it]";
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

	/** The target checkpoints of the transition the failed search got stuck on, with what each one demands. */
	private String describeTargets() {
		if (mDeepestStep < 0 || mDeepestStep >= mSteps) {
			return "none";
		}
		final StringBuilder sb = new StringBuilder();
		for (final CallNode<STATE> target : mSystem.getTransition(mWitness.getTransitionId(mDeepestStep))
				.getTargetStates()) {
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
	 * The states from which some target of {@code transition} is still reachable. Prunes the search away from
	 * parts of the automaton that cannot end this step at all. Call and return transitions count as edges here:
	 * over-approximating reachability only weakens the pruning, it can never rule out a real path.
	 */
	private Set<STATE> canReachATargetOf(final Transition<CallNode<STATE>> transition) {
		return mCanReachTarget.computeIfAbsent(transition.getId(), id -> {
			final Map<STATE, List<STATE>> predecessors = predecessors();
			final Set<STATE> result = new HashSet<>(statesOf(transition.getTargetStates()));
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

	private void checkBudget() {
		mExpansions++;
		if (mExpansions > MAX_EXPANSIONS) {
			throw new KInductionCounterexampleException("gave up reconstructing a counterexample after "
					+ MAX_EXPANSIONS + " expansions for " + mWitness);
		}
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
		mLogger.info("KInduction: reconstructed a counterexample of %d letter(s), %d of them call(s), after %d "
				+ "expansion(s)", mLetters.size(), countCalls(), mExpansions);
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
