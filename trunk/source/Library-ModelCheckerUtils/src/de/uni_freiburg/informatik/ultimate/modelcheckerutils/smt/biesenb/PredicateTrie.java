/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Data structure that stores predicates in a tree, to check for equivalent predicates in a efficient way
 *
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class PredicateTrie<T extends IPredicate> {
	private final T mTruePredicate;
	private final T mFalsePredicate;
	private final IIcfgSymbolTable mSymbolTable;
	private final ManagedScript mMgdScript;

	private IVertex mRoot;

	protected PredicateTrie(final ManagedScript script, final T truePredicate, final T falsePredicate,
			final IIcfgSymbolTable symbolTable) {
		mMgdScript = script;
		mSymbolTable = symbolTable;
		mTruePredicate = truePredicate;
		mFalsePredicate = falsePredicate;
		mRoot = null;
	}

	protected int getDepth() {
		if (mRoot == null) {
			return 0;
		}
		return getDepthHelper(mRoot, 0);
	}

	private int getDepthHelper(final IVertex vertex, final int depth) {
		if (vertex instanceof PredicateVertex) {
			return depth + 1;
		}
		final int trueMaxDepth = getDepthHelper(((ModelVertex) vertex).getChild(false), depth + 1);
		final int falseMaxDepth = getDepthHelper(((ModelVertex) vertex).getChild(true), depth + 1);
		return Math.max(trueMaxDepth, falseMaxDepth);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		stringHelper(mRoot, sb);
		return sb.toString();
	}

	private void stringHelper(final IVertex vertex, StringBuilder sb) {
		if (vertex instanceof ModelVertex) {
			sb.append(vertex.print() + "\n");
			stringHelper(((ModelVertex) vertex).getChild(true), sb);
			stringHelper(((ModelVertex) vertex).getChild(false), sb);
		}
	}

	/*
	 * protected boolean isRepresentative(final T predicate) { // check for true/false if
	 * (mTruePredicate.equals(predicate) || mFalsePredicate.equals(predicate)) return true; // empty tree if (mRoot ==
	 * null) return false; IVertex current = mRoot; // find the predicate with the same fulfilling models while (current
	 * instanceof ModelVertex) { final boolean edge = fulfillsPredicate(predicate, ((ModelVertex)current).getWitness());
	 * current = ((ModelVertex)current).getChild(edge); }
	 *
	 * @SuppressWarnings("unchecked") final T currentPredicate = ((PredicateVertex<T>) current).mPredicate; return
	 * currentPredicate.equals(predicate); }
	 */

	protected Collection<T> unifyPredicateCollection(final Collection<T> predicates) {
		final Collection<T> unifiedSet = new HashSet<>();
		predicates.forEach(p -> unifiedSet.add(unifyPredicate(p)));
		return unifiedSet;
	}

	protected Map<Term, Term> getWitness(final T fulfill, final Set<T> unfulfill) {
		final Script script = mMgdScript.getScript();
		final Collection<Term> unfulfillTerms = new HashSet<>();
		unfulfill.forEach(p -> unfulfillTerms.add(p.getFormula()));
		Term joined = script.term("true");
		if (!unfulfillTerms.isEmpty()) {
			unfulfillTerms.add(mFalsePredicate.getFormula());
			joined = script.term("not", script.term("or", unfulfillTerms.toArray(new Term[unfulfillTerms.size()])));
		}
		final Term all = script.term("and", fulfill.getFormula(), joined);
		return getWitness(all);
	}

	/**
	 * @returns the equivalent predicate, if there is no such predicate the given one is added and returned
	 */
	protected T unifyPredicate(final T predicate) {
		// empty tree
		if (mRoot == null) {
			mRoot = new PredicateVertex<>(predicate);
			return predicate;
		}
		IVertex current = mRoot;
		ModelVertex parent = null;
		// find the predicate with the same fulfilling models
		while (current instanceof ModelVertex) {
			parent = (ModelVertex) current;
			final boolean edge = fulfillsPredicate(predicate, parent.getWitness());
			current = parent.getChild(edge);
		}
		@SuppressWarnings("unchecked")
		final T currentPredicate = ((PredicateVertex<T>) current).mPredicate;
		final Map<Term, Term> newWitness = compare(predicate, currentPredicate);
		// an equal predicate is already in the tree
		if (newWitness.isEmpty()) {
			return currentPredicate;
		}
		// the given predicate is new and inserted to the tree
		final ModelVertex newNode = fulfillsPredicate(predicate, newWitness)
				? new ModelVertex(new PredicateVertex<>(predicate), current, newWitness)
				: new ModelVertex(current, new PredicateVertex<>(predicate), newWitness);
		if (parent != null) {
			parent.swapChild(current, newNode);
		} else {
			mRoot = newNode;
		}
		return predicate;
	}

	protected T removePredicate(final T predicate) {
		boolean edge;
		if (mRoot == null) {
			return null;
		}
		if (mRoot == predicate) {
			mRoot = null;
			return predicate;
		}
		IVertex current = mRoot;
		ModelVertex grandParent = null;
		ModelVertex parent = null;
		// find the predicate
		while (current instanceof ModelVertex) {
			grandParent = parent;
			parent = (ModelVertex) current;
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

	/**
	 * check if model fulfills predicate
	 */
	protected boolean fulfillsPredicate(final T predicate, final Map<Term, Term> witness) {
		final SubstitutionWithLocalSimplification subst = new SubstitutionWithLocalSimplification(mMgdScript, witness);
		final Term result = subst.transform(predicate.getClosedFormula());
		return mTruePredicate.getFormula().equals(result);
	}

	/**
	 * check if predicates are equal
	 */
	protected Map<Term, Term> compare(final T predicate, final T leafPredicate) {
		final T localPred = leafPredicate;
		final Term local = localPred.getClosedFormula();
		final Term other = predicate.getClosedFormula();
		// TODO replace with getWitness()
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		mMgdScript.lock(this);
		final Term isEqual = mMgdScript.term(this, "distinct", local, other);
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, isEqual);
			final LBool result = mMgdScript.checkSat(this);
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
				return mMgdScript.getScript().getValue(terms.toArray(new Term[terms.size()]));
			} else {
				throw new UnsupportedOperationException(
						"Cannot handle case were solver cannot decide equality of predicates");
			}
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
	}

	private Map<Term, Term> getWitness(final Term term) {
		final TermVarsProc termVarsProc = TermVarsProc.computeTermVarsProc(term, mMgdScript.getScript(), mSymbolTable);
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, termVarsProc.getClosedFormula());
			final LBool result = mMgdScript.checkSat(this);
			if (result == LBool.SAT) {
				final Set<IProgramVar> vars = termVarsProc.getVars();
				final Set<ApplicationTerm> terms =
						vars.stream().map(IProgramVar::getDefaultConstant).collect(Collectors.toSet());
				return mMgdScript.getScript().getValue(terms.toArray(new Term[terms.size()]));
			} else {
				throw new UnsupportedOperationException("Solver cannot find a model for the term " + term);
			}
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
	}

	public boolean constructTrie(Pair<Integer, Map<Term, Term>> root, 
			Map<Pair<Integer, Map<Term, Term>>, Pair<Pair<Integer, Map<Term, Term>>, 
			Pair<Integer, Map<Term, Term>>>> witnesses,
			Map<Term, T> preds) {
		//trie must be empty
		if(mRoot != null) return false;
		Map<Pair<Integer, Map<Term, Term>>, ModelVertex> modelVertices = new HashMap<>();
		
		for(Pair<Integer, Map<Term, Term>> key : witnesses.keySet()) {
			modelVertices.put(key, new ModelVertex(null, null, key.getSecond()));
		}
		for(Map.Entry<Pair<Integer, Map<Term, Term>>, Pair<Pair<Integer, Map<Term, Term>>, 
				Pair<Integer, Map<Term, Term>>>> entry : witnesses.entrySet()) {
			 Pair<Pair<Integer, Map<Term, Term>>, Pair<Integer, Map<Term, Term>>> children = entry.getValue();
			if(children.getFirst().getFirst().equals(-1)){
				// predicate
				IVertex trueChild = new PredicateVertex(preds.get(children.getFirst().getSecond().keySet().iterator().next()));
				modelVertices.get(entry.getKey()).setTrueChild(trueChild);
			} else {
				// model
				modelVertices.get(entry.getKey()).setTrueChild(modelVertices.get(children.getFirst()));
			}
			if(children.getSecond().getFirst().equals(-1)){
				// predicate
				IVertex falseChild = new PredicateVertex(preds.get(children.getSecond().getSecond().keySet().iterator().next()));
				modelVertices.get(entry.getKey()).setFalseChild(falseChild);
			} else {
				// model
				modelVertices.get(entry.getKey()).setFalseChild(modelVertices.get(children.getSecond()));
			}
		}
		mRoot = modelVertices.get(root);
		return true;
	}
}