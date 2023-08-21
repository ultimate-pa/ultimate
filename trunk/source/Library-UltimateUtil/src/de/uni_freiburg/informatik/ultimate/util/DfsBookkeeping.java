/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Manages book-keeping data for depth-first traversal of a graph with sophisticated loop detection. This loop detection
 * allows to distinguish backtracking because all reachable nodes have been explored from backtracking inside a loop,
 * where perhaps some reachable nodes have not yet been explored.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <V>
 *            The type of nodes in the traversed graph
 */
public class DfsBookkeeping<V> {
	public final List<V> mStack = new ArrayList<>();

	// Maps each visited node v to the outermost loop head reached from v, and its stack index.
	// If v has no entry, it has not been visited. If v is mapped to null, no loop head has been reached from v.
	// When backtracking v, this is used to determine if all nodes reachable from v have been explored, or if this may
	// not be the case because v is in a loop.
	private final Map<V, Pair<Integer, V>> mVisited2LoopHeadIndex = new HashMap<>();

	/**
	 * Determines if the given node has already been visited.
	 */
	public boolean isVisited(final V node) {
		return mVisited2LoopHeadIndex.containsKey(node);
	}

	/**
	 * Determines if the DFS has started, i.e., if any node has been visited so far.
	 */
	public boolean hasStarted() {
		return !mVisited2LoopHeadIndex.isEmpty();
	}

	/**
	 * Determines if the stack is empty.
	 */
	public boolean isStackEmpty() {
		return mStack.isEmpty();
	}

	/**
	 * Returns the index of the given node in the stack (the bottom element has index 0, the top element's index is the
	 * biggest). Returns -1 if the node is not on the stack.
	 */
	public int stackIndexOf(final V node) {
		return mStack.indexOf(node);
	}

	/**
	 * Pushes the given node on the DFS stack.
	 *
	 * @return true if this is the first visit to the node, false otherwise.
	 */
	public boolean push(final V node) {
		final boolean visitedBefore = isVisited(node);
		if (!visitedBefore) {
			mVisited2LoopHeadIndex.put(node, null);
		}

		assert !mStack.contains(node) : "must not infinitely unroll loop";
		mStack.add(node);
		return !visitedBefore;
	}

	/**
	 * Retrieves the top element of the DFS stack.
	 */
	public V peek() {
		return mStack.get(mStack.size() - 1);
	}

	private V pop() {
		return mStack.remove(mStack.size() - 1);
	}

	/**
	 * Backtracks the top node on the stack.
	 *
	 * @return true if the node is backtracked completely, i.e., all nodes reachable from it have been explored, and
	 *         were not ignored because the node is part of a loop.
	 */
	public boolean backtrack() {
		final V oldNode = pop();
		assert isVisited(oldNode) : "stack node must have been visited";

		Pair<Integer, V> loopHead = mVisited2LoopHeadIndex.get(oldNode);
		if (loopHead != null && loopHead.getSecond() == oldNode) {
			// The outermost loop head can be backtracked completely.
			mVisited2LoopHeadIndex.put(oldNode, null);
			loopHead = null;
		}

		// If there is a loop head, propagate it to the predecessor.
		if (loopHead != null) {
			assert !mStack.isEmpty() : "Initial node must not be in a loop (except as loop head)";
			assert validLoopHead(loopHead) : "Backtracked node's loop head must be higher on the stack";
			updateLoopHead(peek(), loopHead);
		}

		// Determine if we are backtracking inside a loop, or if the backtrack is "complete".
		return loopHead == null;
	}

	/**
	 * Updates the stored loop head for a given node. I.e., if there is an existing loop head, the loop head deeper on
	 * the stack is kept. If there is no existing loop head, sets the node's loop head to the given one.
	 */
	public void updateLoopHead(final V node, final Pair<Integer, V> newLoopHead) {
		assert mStack.contains(node) : "loop head can only be updated for stack nodes";
		assert isVisited(node) : "loop head can only be updated for visited nodes";
		assert validLoopHead(newLoopHead) : "new loop head is invalid";

		final Pair<Integer, V> oldLoopHead = mVisited2LoopHeadIndex.get(node);
		assert oldLoopHead == null || validLoopHead(oldLoopHead) : "old loop head has become invalid";

		if (oldLoopHead == null || newLoopHead.getFirst() < oldLoopHead.getFirst()) {
			mVisited2LoopHeadIndex.put(node, newLoopHead);
		}
	}

	/**
	 * When encountering an edge to a previously visited node, propagates loop head information from the successor node
	 * of the edge back to the current node.
	 */
	public void backPropagateLoopHead(final V current, final V successor) {
		final Pair<Integer, V> loopHead = getStackedLoopHead(successor);
		if (loopHead != null) {
			updateLoopHead(current, loopHead);
		}
	}

	private Pair<Integer, V> getStackedLoopHead(final V node) {
		int currentIndex = Integer.MAX_VALUE;
		V currentNode = node;

		while (true) {
			assert currentIndex >= 0 : "negative loop head index";
			assert isVisited(currentNode) : "encountered unvisited node in loop head chain";

			final Pair<Integer, V> loopHead = mVisited2LoopHeadIndex.get(currentNode);
			if (loopHead == null || validLoopHead(loopHead)) {
				return loopHead;
			}

			final V loopHeadNode = loopHead.getSecond();
			if (loopHeadNode == currentNode) {
				return null;
			}

			assert loopHead.getFirst() < currentIndex : "loop head index must decrease";
			currentIndex = loopHead.getFirst();
			currentNode = loopHeadNode;
		}
	}

	private boolean validLoopHead(final Pair<Integer, V> loopHead) {
		return loopHead.getFirst() < mStack.size() && mStack.get(loopHead.getFirst()) == loopHead.getSecond();
	}
}
