/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PredicateTree<T extends IPredicate> {

	private final Term mTrue;
	private final Term mFalse;

	private final ManagedScript mScript;
	private INode<T> mRoot;

	public PredicateTree(final ManagedScript script) {
		this(script, script.getScript().term("true"), script.getScript().term("false"));
	}

	public PredicateTree(final ManagedScript script, final Term trueTerm, final Term falseTerm) {
		assert script != null;
		mScript = script;
		mTrue = trueTerm;
		mFalse = falseTerm;
		mRoot = null;
	}

	public T unifyPredicate(final T predicate) {
		if (predicate == null) {
			return null;
		}
		if (mRoot == null) {
			mRoot = new Leaf(predicate);
			return predicate;
		}
		if (mRoot instanceof PredicateTree.Leaf) {
			return unifyAndUpdate((Leaf) mRoot, null, predicate);
		}

		INode<T> current = mRoot;
		INode<T> last = current;
		while (current != null) {
			final INode<T> next = current.next(predicate);
			if (next != null) {
				// current is an inner node, follow it
				last = current;
				current = next;
				continue;
			}
			return unifyAndUpdate((Leaf) current, (InnerNode) last, predicate);
		}
		throw new AssertionError("Should be unreachable");
	}

	public String toLogString() {
		if (mRoot == null) {
			return "";
		}
		final StringBuilder sb = new StringBuilder();
		final Deque<Pair<String, INode<T>>> worklist = new ArrayDeque<>();
		worklist.addFirst(new Pair<>("", mRoot));
		while (!worklist.isEmpty()) {
			final Pair<String, INode<T>> currentP = worklist.removeFirst();
			final INode<T> current = currentP.getSecond();
			if (current instanceof PredicateTree.Leaf) {
				sb.append(currentP.getFirst());
				sb.append(current.toString());
				sb.append("\n");
				continue;
			}

			final InnerNode inner = ((PredicateTree<T>.InnerNode) current);
			sb.append(currentP.getFirst());
			sb.append(inner.toString());
			sb.append("\n");
			final String newId = currentP.getFirst() + " ";
			worklist.addFirst(new Pair<>(newId, inner.mLeftChild));
			worklist.addFirst(new Pair<>(newId, inner.mRightChild));
		}
		return sb.toString();
	}

	private T unifyAndUpdate(final Leaf leaf, final InnerNode parent, final T predicate) {
		// current is a leaf, perform actual unification
		final Pair<T, Map<Term, Term>> unificationResult = unify(leaf.mPredicate, predicate);
		if (unificationResult.getFirst() == leaf.mPredicate) {
			// it was equal, we are finished
			return leaf.mPredicate;
		}

		// it was not equal, we have to update the tree
		final InnerNode subtree = newSubTree(leaf, predicate, unificationResult.getSecond());

		if (parent == null) {
			// we have to update root
			mRoot = subtree;
		} else {
			// we have to update a subtree
			final boolean isLeftLeaf = parent.mLeftChild == leaf;

			if (isLeftLeaf) {
				parent.mLeftChild = subtree;
			} else {
				parent.mRightChild = subtree;
			}
		}

		return predicate;
	}

	private Pair<T, Map<Term, Term>> unify(final T leafPredicate, final T predicateToUnify) {
		final T localPred = leafPredicate;
		final Term local = localPred.getClosedFormula();
		final Term other = predicateToUnify.getClosedFormula();
		mScript.lock(this);
		final Term isEqual = mScript.term(this, "distinct", local, other);
		mScript.push(this, 1);
		try {
			mScript.assertTerm(this, isEqual);
			final LBool result = mScript.checkSat(this);
			if (result == LBool.UNSAT) {
				// they are equal
				return new Pair<>(localPred, null);
			} else if (result == LBool.SAT) {
				// they are not equal
				final Set<IProgramVar> vars = new HashSet<>();
				vars.addAll(predicateToUnify.getVars());
				vars.addAll(localPred.getVars());
				final Set<ApplicationTerm> terms =
						vars.stream().map(IProgramVar::getDefaultConstant).collect(Collectors.toSet());

				// this is a witness that should be accepted by one and rejected by the other
				final Map<Term, Term> witness = mScript.getScript().getValue(terms.toArray(new Term[terms.size()]));
				return new Pair<>(predicateToUnify, witness);
			} else {
				throw new UnsupportedOperationException(
						"Cannot handle case were solver cannot decide equality of predicates");
			}
		} finally {
			mScript.pop(this, 1);
			mScript.unlock(this);
		}
	}

	private PredicateTree<T>.InnerNode newSubTree(final Leaf oldLeaf, final T newPredicate,
			final Map<Term, Term> witness) {
		final Leaf newLeaf = new Leaf(newPredicate);
		if (goLeft(witness, newPredicate)) {
			return new InnerNode(newLeaf, oldLeaf, witness);
		}
		return new InnerNode(oldLeaf, newLeaf, witness);
	}

	private boolean goLeft(final Map<Term, Term> witness, final T predicate) {
		final SubstitutionWithLocalSimplification subst = new SubstitutionWithLocalSimplification(mScript, witness);
		final Term result = subst.transform(predicate.getClosedFormula());
		return mTrue.equals(result);
	}

	@FunctionalInterface
	private interface INode<T> {
		INode<T> next(T predicate);
	}

	private final class InnerNode implements INode<T> {
		private final Map<Term, Term> mWitness;
		private INode<T> mLeftChild;
		private INode<T> mRightChild;

		private InnerNode(final INode<T> left, final INode<T> right, final Map<Term, Term> witness) {
			assert witness != null && !witness.isEmpty();
			assert left != null;
			assert right != null;
			mWitness = witness;
			mLeftChild = left;
			mRightChild = right;
		}

		@Override
		public INode<T> next(final T predicate) {
			if (goLeft(mWitness, predicate)) {
				return mLeftChild;
			}
			return mRightChild;
		}

		@Override
		public String toString() {
			return mWitness.toString();
		}
	}

	private final class Leaf implements INode<T> {
		private final T mPredicate;

		private Leaf(final T pred) {
			assert pred != null;
			mPredicate = pred;
		}

		@Override
		public INode<T> next(final T predicate) {
			return null;
		}

		@Override
		public String toString() {
			return mPredicate.toString();
		}
	}

}
