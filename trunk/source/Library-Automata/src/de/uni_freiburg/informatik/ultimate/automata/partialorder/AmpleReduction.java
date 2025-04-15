/*
 * Copyright (C) 2025 Veronika Klasen
 * Copyright (C) 2025 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.DfsBookkeeping;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * DFS with ample sets. Only applicable to deterministic input automata in which every state is final.
 *
 * @param <L>
 *            The type of letters in the traversed automaton
 * @param <S>
 *            The type of states in the traversed automaton
 */
public class AmpleReduction<L, S> {
	private static final String ABORT_MSG = "visitor aborted traversal";

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final S mStartState;
	private final IDfsOrder<L, S> mOrder;
	private final IDfsVisitor<L, S> mVisitor;
	private final IPersistentSetChoice<L, S> mPersistent;

	private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();
	private final DfsBookkeeping<S> mDfs = new DfsBookkeeping<>();

	// to check if input automaton only has final states
	// TODO Why introduce a separate field for this? We could just call mOperand.isFinal(...) directly.
	private final Predicate<S> mIsFinal;

	// Used to store the ample sets of the reduction state. Note that the trivial ample set (set of all outgoing edges)
	// is represented by null.
	private final Map<S, Set<L>> mAmpleSets = new HashMap<>();

	// cache nodes from with trivial ample set
	// TODO: think about whether to remove trivial nodes cache altogether
	private final Set<S> mTrivialNodes = new HashSet<>();

	// TODO Move statistics-related field into a statistics class
	// count number of incidents where upon fist discovery, a node was identified as a loop node and upon a subsequent
	// discovery wasn't
	private int mLoopNotLoopCount;
	// count number of nodes that were assigned non-trivial ample set on first encounter
	private int mAssignedNonTrivialAmple;
	private int mPrunedTS;
	private int mPersistentTrivial;
	private int mTargetAlreadyLN;
	private int mSomeOtherNodeOnCycleAlreadyLN;
	// number of times a trivial set was assigned bc of node being a loop node
	private int mLoopCausedTrivial;

	private int mIndentLevel = -1;

	/**
	 * Do a DFS-traversal on the ample set reduction of the input automaton. This constructor is called purely for its
	 * side-effects.
	 *
	 * @param services
	 *            automata services used for logging and timeout management
	 * @param operand
	 *            The automaton to be traversed
	 * @param order
	 *            The order in which transitions for each state should be explored
	 * @param visitor
	 *            A visitor to traverse the automaton
	 * @param startingState
	 *            A state from which the traversal starts.
	 * @param persistent
	 *            Persistent sets used to compute ample sets
	 * @throws AutomataOperationCanceledException
	 *             in case of timeout or cancellation
	 */
	public AmpleReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IDfsOrder<L, S> order,
			final IDfsVisitor<L, S> visitor, final S startingState, final IPersistentSetChoice<L, S> persistent)
			throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "DFS supports only finite automata";
		mServices = services;
		mLogger = services.getLoggingService().getLogger(AmpleReduction.class);

		mOperand = operand;
		mStartState = startingState;
		mOrder = order;
		mVisitor = visitor;
		mPersistent = persistent;
		mIsFinal = operand::isFinal;

		mLogger.info("Starting ample reduction");
		mAmpleSets.put(mStartState, mPersistent.persistentSet(startingState));
		traverse();

		// TODO move statistics fields into a Statistics class & print it here, but also return from #getStatistics()
		mLogger.warn("Number of pruned transitions: " + mPrunedTS);
		mLogger.warn("Loop nodes with \"changing loop node status\": %s ", mLoopNotLoopCount);
		mLogger.warn("Number of trivial sets caused by loops: " + mLoopCausedTrivial);
		mLogger.warn("Number of not loop caused trivial ample sets:" + mPersistentTrivial);
		mLogger.warn("Number of  initially assigned non-trivial ample sets:" + mAssignedNonTrivialAmple);
		mLogger.warn("Times succ was already a loop node:" + mTargetAlreadyLN);
		mLogger.warn(
				"Times some other node on the cycle alrdy had a trivial ample set:" + mSomeOtherNodeOnCycleAlreadyLN);

		mLogger.info("Finished ample reduction");
	}

	/**
	 * Performs a depth-first traversal starting from the operand's initial state. This method is called purely for its
	 * side-effects.
	 *
	 * @param services
	 *            automata services used for logging and timeout management
	 * @param operand
	 *            The automaton to be traversed
	 * @param order
	 *            The order in which transitions for each state should be explored
	 * @param visitor
	 *            A visitor to traverse the automaton
	 * @param persistent
	 *            Persistent sets used to compute ample sets
	 * @throws AutomataOperationCanceledException
	 *             in case of timeout or cancellation
	 */
	public static <L, S> void traverse(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IDfsOrder<L, S> order,
			final IDfsVisitor<L, S> visitor, final IPersistentSetChoice<L, S> persistent)
			throws AutomataOperationCanceledException {
		final var initial =
				DataStructureUtils.getOnly(operand.getInitialStates(), "There must only be one initial state");
		if (initial.isPresent()) {
			new AmpleReduction<>(services, operand, order, visitor, initial.get(), persistent);
		} else {
			final var logger = services.getLoggingService().getLogger(AmpleReduction.class);
			logger.warn("Depth first traversal did not find any initial state. Returning directly.");
		}
	}

	private void traverse() throws AutomataOperationCanceledException {
		final boolean abortImmediately = visitState(mStartState);
		if (abortImmediately) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		while (!mWorklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final var current = mWorklist.pop();
			final S currentState = current.getFirst();

			// Backtrack states still on the stack whose exploration has finished.
			final boolean abort = backtrackUntil(currentState);
			if (abort) {
				mLogger.debug(ABORT_MSG);
				return;
			}

			final OutgoingInternalTransition<L, S> currentTransition = current.getSecond();
			final S nextState = currentTransition.getSucc();
			debugIndent("Now exploring transition %s --> %s (label: %s)", currentState, nextState,
					currentTransition.getLetter());

			// ------------------------------------------ ample red stuff ----------------------------------------------
			assert mAmpleSets.containsKey(currentState) : "Ample set for this state should have been already computed.";
			assert mIsFinal.test(currentState) : "All states of the automaton should be final!";

			final Set<L> currentAmple = mAmpleSets.get(currentState);
			final L letter = currentTransition.getLetter();
			final boolean prune;

			// Prune outgoing edges not in the state's ample set
			if (currentAmple != null && !currentAmple.contains(letter)) {
				prune = true;
			} else {
				// compute ample set for next state
				// TODO refactor this into one or probably more separate methods
				if (!mTrivialNodes.contains(nextState)) {
					// TODO Finde heraus, warum die Reduktionen soviel größer sind, als sie mit dem AmpleRedVisitor
					// waren
					// check for all outgoing transitions of next state if they'd close a cycle
					for (final OutgoingInternalTransition<L, S> currentTS : mOperand.internalSuccessors(nextState)) {
						// TODO Dominik: It is still very confusing to me that we look already look at the outgoing
						// transitions of nextState here (i.e., we look 2 states ahead of the current state).
						// Intuitively, it would make more sense to me if the computation of the ample set for nextState
						// would happen inside the visitState() method (when and if it is called with parameter
						// nextState below).
						// TODO If there are reasons why it has to be done here, please explain them in comments.

						// we're in theory only interested in loops in the reduction automaton. in practice there's
						// hardly a difference
						// TODO Dominik: Elaborate this comment more: difference compared with what? What does the code
						// implement, the "theoretical" or the "practical version"?
						boolean inAmple = true;
						if (mAmpleSets.containsKey(nextState)) {
							final Set<L> oldNextAmple = mAmpleSets.get(nextState);
							inAmple = !Objects.isNull(oldNextAmple) && oldNextAmple.contains(currentTS.getLetter());
						}

						// it seems finding the stack index is rather time consuming
						// TODO If this overhead is significant, we should discuss using an improved data structure.
						final int stackIndex;
						if (inAmple && mDfs.isVisited(currentTS.getSucc())
								&& (stackIndex = mDfs.stackIndexOf(currentTS.getSucc())) != -1) {
							final var loop = mDfs.getStackSince(stackIndex);

							// TODO make this more readable
							// Check if any node on loop already has a trivial ample set
							if (mAmpleSets.get(currentTS.getSucc()) == null) {
								// it is so often the case that the target node already has a trivial ample set that it
								// seemed worthwhile to measure separately
								mTargetAlreadyLN++;
								assert mAmpleSets.containsKey(currentTS.getSucc())
										: "missing ample set for successor node on stack";
								continue;
							}
							if (loop.stream().anyMatch(nodeOnCycle -> mAmpleSets.get(nodeOnCycle) == null)) {
								assert loop.stream().allMatch(mAmpleSets::containsKey)
										: "missing ample set for node on stack";
								mSomeOtherNodeOnCycleAlreadyLN++;
								continue;
							}

							mTrivialNodes.add(nextState);
							final var oldAmple = mAmpleSets.put(nextState, null);
							mLoopCausedTrivial++;
							if (oldAmple != null) {
								mLoopNotLoopCount++;
								mLogger.warn("Non-loop node is now a loop node: " + nextState);
							}
							break;
						}
					}
				}
				// compute ample set if that was not already done
				if (!mAmpleSets.containsKey(nextState)) {
					// counting for statistics
					final var nextAmple = mPersistent.persistentSet(nextState);
					if (nextAmple != null) {
						mAssignedNonTrivialAmple++;
					} else {
						mPersistentTrivial++;
						mTrivialNodes.add(nextState);
					}
					mAmpleSets.put(nextState, nextAmple);
				}
				prune = mVisitor.discoverTransition(currentState, currentTransition.getLetter(), nextState);
			}
			// ---------------------------------------- end of ample red stuff -----------------------------------------

			if (mVisitor.isFinished()) {
				mLogger.debug(ABORT_MSG);
				return;
			}

			final int stackIndex;
			if (prune) {
				mPrunedTS++;
				debugIndent("-> transition was pruned");
			} else if (!mDfs.isVisited(nextState)) {
				final boolean abortNow = visitState(nextState);
				if (abortNow) {
					mLogger.debug(ABORT_MSG);
					return;
				}
			} else if ((stackIndex = mDfs.stackIndexOf(nextState)) != -1) {
				debugIndent("-> state is on stack -- do not unroll loop");
				mDfs.updateLoopHead(currentState, new Pair<>(stackIndex, nextState));
			} else {
				debugIndent("-> state was visited before -- no re-exploration");
				mDfs.backPropagateLoopHead(currentState, nextState);
			}
		}

		final boolean abort = backtrackUntil(mStartState);
		if (abort) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		backtrack();
		mLogger.debug("traversal completed");
	}

	private boolean backtrackUntil(final S state) {
		while (!mDfs.peek().equals(state)) {
			final boolean abort = backtrack();
			if (abort) {
				return true;
			}
		}
		return false;
	}

	private boolean backtrack() {
		final S oldState = mDfs.peek();
		final boolean isComplete = mDfs.backtrack();

		debugIndent("backtracking state %s (complete: %s)", oldState, isComplete);
		mIndentLevel--;

		mVisitor.backtrackState(oldState, isComplete);
		return mVisitor.isFinished();
	}

	private boolean visitState(final S state) {
		assert !mDfs.isVisited(state) : "must never re-visit state";
		mIndentLevel++;
		debugIndent("visiting state %s", state);

		final boolean pruneSuccessors;
		if (mStartState.equals(state)) {
			debugIndent("-> state is start state");
			assert !mDfs.hasStarted() : "start state should be first visited state";
			pruneSuccessors = mVisitor.addStartState(state);
		} else {
			assert mDfs.hasStarted() : "first visited state should be start state";
			pruneSuccessors = mVisitor.discoverState(state);
		}
		if (mVisitor.isFinished()) {
			return true;
		}
		mDfs.push(state);

		if (pruneSuccessors) {
			debugIndent("-> visitor pruned all outgoing edges");
		} else {
			// TODO check action determinism here?
			final Comparator<OutgoingInternalTransition<L, S>> comp =
					Comparator.<OutgoingInternalTransition<L, S>, L> comparing(OutgoingInternalTransition::getLetter,
							mOrder.getOrder(state)).reversed();
			StreamSupport.stream(mOperand.internalSuccessors(state).spliterator(), false).sorted(comp)
					.forEachOrdered(out -> mWorklist.push(new Pair<>(state, out)));
		}
		return false;
	}

	private void debugIndent(final String msg, final Object... params) {
		mLogger.debug("  ".repeat(mIndentLevel) + msg, params);
	}
}
