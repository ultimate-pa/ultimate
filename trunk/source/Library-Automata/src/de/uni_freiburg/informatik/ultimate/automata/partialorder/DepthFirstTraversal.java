/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implements a depth-first traversal of deterministic finite automata.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the traversed automaton
 * @param <S>
 *            The type of states in the traversed automaton
 */
public class DepthFirstTraversal<L, S> {
	private final ILogger mLogger;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IDfsOrder<L, S> mOrder;
	private final IDfsVisitor<L, S> mVisitor;

	private final List<S> mStateStack = new ArrayList<>();
	private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();

	// Maps each visited state q to the outermost loop head reached from q, and its state stack index.
	// If q has no entry, it has not been visited. If q is mapped to null, no loop head has been reached from q.
	// When backtracking q, this is used to determine if all states reachable from q have been explored, or if this may
	// not be the case because q is in a loop.
	private final Map<S, Pair<Integer, S>> mVisited2LoopHeadIndex = new HashMap<>();

	private int mIndentLevel = -1;

	/**
	 * Performs a depth-first traversal. This constructor is called purely for its side-effects.
	 *
	 * @param operand
	 *            The automaton to be traversed
	 * @param order
	 *            The order in which transitions for each state should be explored
	 * @param visitor
	 *            A visitor to traverse the automaton
	 */
	public DepthFirstTraversal(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IDfsOrder<L, S> order,
			final IDfsVisitor<L, S> visitor) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "DFS supports only finite automata";

		mLogger = services.getLoggingService().getLogger(DepthFirstTraversal.class);
		mOperand = operand;
		mOrder = order;
		mVisitor = visitor;

		traverse();
	}

	private void traverse() {
		final S initial = DataStructureUtils.getOneAndOnly(mOperand.getInitialStates(), "initial state");
		visitState(initial);

		while (!mWorklist.isEmpty()) {
			final var current = mWorklist.pop();
			final S currentState = current.getFirst();

			// Backtrack states still on the stack whose exploration has finished.
			final boolean abort = backtrackUntil(currentState);
			if (abort) {
				mLogger.debug("visitor aborted search");
				return;
			}

			final OutgoingInternalTransition<L, S> currentTransition = current.getSecond();
			final S nextState = currentTransition.getSucc();
			debugIndent("Now exploring transition %s --> %s (label: %s)", currentState, nextState,
					currentTransition.getLetter());
			final boolean prune = mVisitor.discoverTransition(currentState, currentTransition.getLetter(), nextState);
			if (mVisitor.isFinished()) {
				mLogger.debug("visitor aborted search");
				return;
			}

			final int stackIndex;
			if (prune) {
				debugIndent("-> visitor pruned transition");
			} else if (!mVisited2LoopHeadIndex.containsKey(nextState)) {
				final boolean abortNow = visitState(nextState);
				if (abortNow) {
					mLogger.debug("visitor aborted search");
					return;
				}
			} else if ((stackIndex = mStateStack.indexOf(nextState)) != -1) {
				debugIndent("-> state is on stack -- do not explore loop");
				updateLoopHead(currentState, new Pair<>(stackIndex, nextState));
			} else {
				debugIndent("-> state was visited before -- no re-exploration");
				final Pair<Integer, S> loopHead = getStackedLoopHead(nextState);
				if (loopHead != null) {
					updateLoopHead(currentState, loopHead);
				}
			}
		}

		final boolean abort = backtrackUntil(initial);
		if (abort) {
			mLogger.debug("visitor aborted search");
			return;
		}

		backtrack();
		mLogger.debug("search completed");
	}

	private boolean backtrackUntil(final S state) {
		while (!peek().equals(state)) {
			final boolean abort = backtrack();
			if (abort) {
				return true;
			}
		}
		return false;
	}

	private boolean backtrack() {
		final S oldState = pop();

		// Determine if we are backtracking inside a loop, or if the backtrack is "complete".
		assert mVisited2LoopHeadIndex.containsKey(oldState) : "stack node must have been visited";
		final Pair<Integer, S> loopHead = mVisited2LoopHeadIndex.get(oldState);
		final boolean isComplete = loopHead == null || loopHead.getSecond() == oldState;
		debugIndent("backtracking state %s (complete: %s)", oldState, isComplete);

		// If there is a predecessor, and it is (still) inside a loop, propagate the loop head information.
		if (!mStateStack.isEmpty() && loopHead != null && loopHead.getFirst() < mStateStack.size()) {
			final S predecessor = peek();
			updateLoopHead(predecessor, loopHead);
		}

		mVisitor.backtrackState(oldState, isComplete);
		mIndentLevel--;
		return mVisitor.isFinished();

	}

	private boolean visitState(final S state) {
		assert !mVisited2LoopHeadIndex.containsKey(state) : "must never re-visit state";
		mIndentLevel++;
		debugIndent("visiting state %s", state);

		final boolean pruneSuccessors;
		if (mOperand.isInitial(state)) {
			debugIndent("-> state is initial");
			assert mVisited2LoopHeadIndex.isEmpty() : "initial state should be first visited state";
			pruneSuccessors = mVisitor.addStartState(state);
		} else {
			pruneSuccessors = mVisitor.discoverState(state);
		}
		if (mVisitor.isFinished()) {
			return true;
		}
		mVisited2LoopHeadIndex.put(state, null);

		assert !mStateStack.contains(state) : "must not infinitely unroll loop";
		mStateStack.add(state);

		if (pruneSuccessors) {
			debugIndent("-> visitor pruned all outgoing edges");
		} else {
			final Comparator<OutgoingInternalTransition<L, S>> comp =
					Comparator.<OutgoingInternalTransition<L, S>, L> comparing(OutgoingInternalTransition::getLetter,
							mOrder.getOrder(state)).reversed();
			StreamSupport.stream(mOperand.internalSuccessors(state).spliterator(), false).sorted(comp)
					.forEachOrdered(out -> mWorklist.push(new Pair<>(state, out)));
		}
		return false;
	}

	private Pair<Integer, S> getStackedLoopHead(final S state) {
		int currentIndex = Integer.MAX_VALUE;
		S currentNode = state;

		while (true) {
			assert currentIndex >= 0 : "negative loop head index";
			assert mVisited2LoopHeadIndex.containsKey(currentNode) : "encountered unvisited state in loop head chain";

			final Pair<Integer, S> loopHead = mVisited2LoopHeadIndex.get(currentNode);
			if (loopHead == null || validLoopHead(loopHead)) {
				return loopHead;
			}

			final S loopHeadNode = loopHead.getSecond();
			if (loopHeadNode == currentNode) {
				return null;
			}

			assert loopHead.getFirst() < currentIndex : "loop head index must decrease";
			currentIndex = loopHead.getFirst();
			currentNode = loopHeadNode;
		}
	}

	private void updateLoopHead(final S state, final Pair<Integer, S> newLoopHead) {
		assert mStateStack.contains(state) : "loop head can only be updated for stack nodes";
		assert mVisited2LoopHeadIndex.containsKey(state) : "loop head can only be updated for visited nodes";
		assert validLoopHead(newLoopHead) : "new loop head is invalid";

		final Pair<Integer, S> oldLoopHead = mVisited2LoopHeadIndex.get(state);
		assert oldLoopHead == null || validLoopHead(oldLoopHead) : "old loop head has become invalid";

		if (oldLoopHead == null || newLoopHead.getFirst() < oldLoopHead.getFirst()) {
			mVisited2LoopHeadIndex.put(state, newLoopHead);
		}
	}

	private boolean validLoopHead(final Pair<Integer, S> loopHead) {
		return loopHead.getFirst() < mStateStack.size() && mStateStack.get(loopHead.getFirst()) == loopHead.getSecond();
	}

	private void debugIndent(final String msg, final Object... params) {
		mLogger.debug(msg.indent(mIndentLevel * 2).stripTrailing(), params);
	}

	private S peek() {
		return mStateStack.get(mStateStack.size() - 1);
	}

	private S pop() {
		return mStateStack.remove(mStateStack.size() - 1);
	}
}
