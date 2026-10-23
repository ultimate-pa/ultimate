/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Creates and manages reduced ordered binary decision diagrams (ROBDDs).
 *
 * Variables are ordered by the order in which they are registered.
 *
 * @param <V>
 *            The type used to identify Boolean variables.
 */
public final class BddManager<V> {

	private static final int TERMINAL_VARIABLE = Integer.MAX_VALUE;

	enum Operation {
		AND, OR
	}

	static final class Node {
		final int mId;
		final int mVariable;
		final Node mLeft;
		final Node mRight;
		final boolean mValue;

		// Nonterminal node.
		Node(final int id, final int variable, final Node low, final Node high) {
			mId = id;
			mVariable = variable;
			mLeft = low;
			mRight = high;
			mValue = false;
		}

		// Terminal node.
		Node(final int id, final boolean value) {
			mId = id;
			mVariable = TERMINAL_VARIABLE;
			mLeft = null;
			mRight = null;
			mValue = value;
		}

		boolean isTerminal() {
			return mVariable == TERMINAL_VARIABLE;
		}
	}

	private record NodeKey(int variable, Node low, Node high) {
	}

	private record ApplyKey(Operation operation, Node left, Node right) {
	}

	final Node mFalseNode = new Node(0, false);
	final Node mTrueNode = new Node(1, true);

	private int mNextNodeId = 2;

	private final Map<V, Integer> mVariableIndices = new HashMap<>();
	private final List<V> mVariables = new ArrayList<>();

	private final Map<NodeKey, Node> mUniqueTable = new HashMap<>();
	private final Map<ApplyKey, Node> mApplyCache = new HashMap<>();
	private final Map<Node, Node> mNotCache = new HashMap<>();

	public BddManager() {
		// The two terminal nodes are created once per manager.
	}

	public Bdd<V> getTrue() {
		return new Bdd<>(this, mTrueNode);
	}

	public Bdd<V> getFalse() {
		return new Bdd<>(this, mFalseNode);
	}

	/**
	 * Returns the BDD variable for the given key, creating it if necessary.
	 */
	public Bdd<V> variable(final V variable) {
		Objects.requireNonNull(variable, "Variable must not be null");

		final int index = mVariableIndices.computeIfAbsent(variable, key -> {
			final int newIndex = mVariables.size();
			mVariables.add(key);
			return newIndex;
		});

		return new Bdd<>(this, makeNode(index, mFalseNode, mTrueNode));
	}

	/**
	 * Registers variables in the supplied order. Call before constructing formulas if a deliberate ordering is desired.
	 */
	public void registerVariables(final Iterable<? extends V> variables) {
		for (final V variable : variables) {
			Objects.requireNonNull(variable, "Variable must not be null");
			if (!mVariableIndices.containsKey(variable)) {
				mVariableIndices.put(variable, mVariables.size());
				mVariables.add(variable);
			}
		}
	}

	V getVariableForIndex(final int index) {
		return mVariables.get(index);
	}

	public Bdd<V> and(final Bdd<V> left, final Bdd<V> right) {
		checkSameManager(left, right);
		return new Bdd<>(this, apply(Operation.AND, left.mRoot, right.mRoot));
	}

	public Bdd<V> or(final Bdd<V> left, final Bdd<V> right) {
		checkSameManager(left, right);
		return new Bdd<>(this, apply(Operation.OR, left.mRoot, right.mRoot));
	}

	public Bdd<V> not(final Bdd<V> operand) {
		checkManager(operand);
		return new Bdd<>(this, negate(operand.mRoot));
	}

	private void checkSameManager(final Bdd<V> left, final Bdd<V> right) {
		checkManager(left);
		checkManager(right);
	}

	private void checkManager(final Bdd<V> bdd) {
		Objects.requireNonNull(bdd);
		if (bdd.mManager != this) {
			throw new IllegalArgumentException("BDD belongs to a different manager");
		}
	}

	/**
	 * Creates a reduced node and reuses any identical node already present.
	 */
	private Node makeNode(final int variable, final Node low, final Node high) {
		// Reduction rule: a redundant test can be removed.
		if (low == high) {
			return low;
		}

		final NodeKey key = new NodeKey(variable, low, high);
		return mUniqueTable.computeIfAbsent(key, ignored -> new Node(mNextNodeId++, variable, low, high));
	}

	private Node apply(final Operation operation, Node left, Node right) {
		// AND and OR are commutative. Normalize the cache key.
		if (left.mId > right.mId) {
			final Node temporary = left;
			left = right;
			right = temporary;
		}

		// Terminal simplifications.
		if (left.isTerminal() && right.isTerminal()) {
			final boolean result = switch (operation) {
			case AND -> left.mValue && right.mValue;
			case OR -> left.mValue || right.mValue;
			};
			return result ? mTrueNode : mFalseNode;
		}

		if (operation == Operation.AND) {
			if (left == mFalseNode || right == mFalseNode) {
				return mFalseNode;
			}
			if (left == mTrueNode) {
				return right;
			}
			if (right == mTrueNode || left == right) {
				return left;
			}
		} else {
			if (left == mTrueNode || right == mTrueNode) {
				return mTrueNode;
			}
			if (left == mFalseNode) {
				return right;
			}
			if (right == mFalseNode || left == right) {
				return left;
			}
		}

		final ApplyKey key = new ApplyKey(operation, left, right);
		final Node cached = mApplyCache.get(key);
		if (cached != null) {
			return cached;
		}

		// Follow the earliest variable in the fixed variable ordering.
		final int topVariable = Math.min(left.mVariable, right.mVariable);

		final Node leftLow = left.mVariable == topVariable ? left.mLeft : left;
		final Node leftHigh = left.mVariable == topVariable ? left.mRight : left;

		final Node rightLow = right.mVariable == topVariable ? right.mLeft : right;
		final Node rightHigh = right.mVariable == topVariable ? right.mRight : right;

		final Node low = apply(operation, leftLow, rightLow);
		final Node high = apply(operation, leftHigh, rightHigh);

		final Node result = makeNode(topVariable, low, high);
		mApplyCache.put(key, result);
		return result;
	}

	private Node negate(final Node node) {
		if (node == mTrueNode) {
			return mFalseNode;
		}
		if (node == mFalseNode) {
			return mTrueNode;
		}

		final Node cached = mNotCache.get(node);
		if (cached != null) {
			return cached;
		}

		final Node result = makeNode(node.mVariable, negate(node.mLeft), negate(node.mRight));

		// Cache both directions: NOT(NOT(f)) = f.
		mNotCache.put(node, result);
		mNotCache.put(result, node);
		return result;
	}

	String toString(final Bdd<V> bdd) {
		checkManager(bdd);
		final StringBuilder result = new StringBuilder();
		appendNode(bdd.mRoot, result);
		return result.toString();
	}

	private void appendNode(final Node node, final StringBuilder result) {
		if (node == mTrueNode) {
			result.append("TRUE");
		} else if (node == mFalseNode) {
			result.append("FALSE");
		} else {
			result.append('(');
			result.append(mVariables.get(node.mVariable));
			result.append(" ? ");
			appendNode(node.mRight, result);
			result.append(" : ");
			appendNode(node.mLeft, result);
			result.append(')');
		}
	}
}