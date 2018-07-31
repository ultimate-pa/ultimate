/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class PredicateTrie<T extends IPredicate> {
	private final Term mTrue;
	private final ManagedScript mScript;
	private INode mRoot;

	public PredicateTrie(final ManagedScript script) {
		mScript = script;
		mTrue = script.getScript().term("true");
		mRoot = null;
	}

	@Override
	public String toString() {
		if (mRoot == null) {
			return "";
		}
		final StringBuilder sb = new StringBuilder();
		mRoot.toString(sb);
		sb.append("\n");
		return sb.toString();
	}

	public T unifyPredicate(final T predicate) {
		// empty tree
		if (mRoot == null) {
			mRoot = new Leaf<>(predicate);
			return predicate;
		}
		INode current = mRoot;
		InnerNode parent = null;
		// find the predicate with the same fulfilling models
		while (current instanceof InnerNode) {
			parent = (InnerNode) current;
			final boolean edge = fulfillsPredicate(predicate, parent.getWitness());
			current = parent.getChild(edge);
		}
		@SuppressWarnings("unchecked")
		final T currentPredicate = ((Leaf<T>) current).mPredicate;
		final Map<Term, Term> newWitness = compare(predicate, currentPredicate);
		// an equal predicate is already in the tree
		if (newWitness.isEmpty()) {
			return currentPredicate;
		}
		// the given predicate is new and inserted to the tree
		final InnerNode newNode =
				fulfillsPredicate(predicate, newWitness) ? new InnerNode(new Leaf<>(predicate), current, newWitness)
						: new InnerNode(current, new Leaf<>(predicate), newWitness);
		if (parent != null) {
			parent.swapChild(current, newNode);
		} else {
			mRoot = newNode;
		}
		return predicate;
	}

	public T removePredicate(final T predicate) {
		boolean edge;
		if (mRoot == null) {
			return null;
		}
		if (mRoot == predicate) {
			mRoot = null;
			return predicate;
		}
		INode current = mRoot;
		InnerNode grandParent = null;
		InnerNode parent = null;
		// find the predicate
		while (current instanceof InnerNode) {
			grandParent = parent;
			parent = (InnerNode) current;
			edge = fulfillsPredicate(predicate, parent.getWitness());
			current = parent.getChild(edge);
		}
		// remove the predicate
		if (current == predicate) {
			edge = fulfillsPredicate(predicate, parent.getWitness());
			if (grandParent == null) {
				mRoot = parent.getChild(!edge);
			} else {
				grandParent.swapChild(parent, parent.getChild(!edge));
			}
			return predicate;
		}
		return null;
	}

	private boolean fulfillsPredicate(final T predicate, final Map<Term, Term> witness) {
		final SubstitutionWithLocalSimplification subst = new SubstitutionWithLocalSimplification(mScript, witness);
		final Term result = subst.transform(predicate.getClosedFormula());
		return mTrue.equals(result);
	}

	private Map<Term, Term> compare(final T predicate, final T leafPredicate) {
		final T localPred = leafPredicate;
		final Term local = localPred.getClosedFormula();
		final Term other = predicate.getClosedFormula();
		mScript.lock(this);
		final Term isEqual = mScript.term(this, "distinct", local, other);
		mScript.push(this, 1);
		try {
			mScript.assertTerm(this, isEqual);
			final LBool result = mScript.checkSat(this);
			if (result == LBool.UNSAT) {
				// they are equal
				return Collections.emptyMap();
			} else if (result == LBool.SAT) {
				// they are not equal
				final Set<IProgramVar> vars = new HashSet<>();
				vars.addAll(predicate.getVars());
				vars.addAll(localPred.getVars());
				final Set<ApplicationTerm> terms =
						vars.stream().map(IProgramVar::getDefaultConstant).collect(Collectors.toSet());
				// this is a witness that should be accepted by one and rejected by the other
				return mScript.getScript().getValue(terms.toArray(new Term[terms.size()]));
			} else {
				throw new UnsupportedOperationException(
						"Cannot handle case were solver cannot decide equality of predicates");
			}
		} finally {
			mScript.pop(this, 1);
			mScript.unlock(this);
		}
	}
}