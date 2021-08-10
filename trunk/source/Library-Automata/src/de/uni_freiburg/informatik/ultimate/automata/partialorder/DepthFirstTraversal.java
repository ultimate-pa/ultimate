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
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
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

	private final Deque<S> mStateStack = new ArrayDeque<>();
	private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();
	private final Set<S> mVisited = new HashSet<>();
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

			if (!prune && !mVisited.contains(nextState)) {
				final boolean abortNow = visitState(nextState);
				if (abortNow) {
					mLogger.debug("visitor aborted search");
					return;
				}
			} else if (prune) {
				debugIndent("-> visitor pruned transition");
			} else {
				debugIndent("-> state was visited before -- no re-exploration");
			}
		}

		final boolean abort = backtrackUntil(initial);
		if (abort) {
			mLogger.debug("visitor aborted search");
			return;
		}

		mStateStack.pop();
		mVisitor.backtrackState(initial, false);
		mLogger.debug("search completed");
	}

	private boolean backtrackUntil(final S state) {
		while (!mStateStack.peek().equals(state)) {
			final S oldState = mStateStack.pop();
			mVisitor.backtrackState(oldState, false);
			mIndentLevel--;
			if (mVisitor.isFinished()) {
				return true;
			}
		}
		return false;
	}

	private boolean visitState(final S state) {
		assert !mVisited.contains(state) : "must never re-visit state";
		mIndentLevel++;
		debugIndent("visiting state %s", state);

		final boolean pruneSuccessors;
		if (mOperand.isInitial(state)) {
			debugIndent("-> state is initial");
			assert mVisited.isEmpty() : "initial state should be first visited state";
			pruneSuccessors = mVisitor.addStartState(state);
		} else {
			pruneSuccessors = mVisitor.discoverState(state);
		}
		if (mVisitor.isFinished()) {
			return true;
		}
		mVisited.add(state);

		assert !mStateStack.contains(state) : "must not infinitely unroll loop";
		mStateStack.push(state);

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

	private void debugIndent(final String msg, final Object... params) {
		mLogger.debug(msg.indent(mIndentLevel * 2).stripTrailing(), params);
	}
}
