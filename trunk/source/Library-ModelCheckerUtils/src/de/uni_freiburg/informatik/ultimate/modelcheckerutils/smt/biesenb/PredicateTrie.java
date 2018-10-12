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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Data structure that stores predicates in a tree, to check for equivalent predicates in a efficient way
 *
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class PredicateTrie<T extends IPredicate> {
	private final IUltimateServiceProvider mServices;
	private final BasicPredicateFactory mFactory;
	private final T mTruePredicate;
	private final T mFalsePredicate;
	private final IIcfgSymbolTable mSymbolTable;
	private final ManagedScript mMgdScript;
	private final ILogger mLogger;
	private final Set<T> mPredicates = new HashSet<>();

	private IVertex mRoot;

	protected PredicateTrie(final ILogger logger, final IUltimateServiceProvider services, final ManagedScript script,
			final T truePredicate, final T falsePredicate, final BasicPredicateFactory factory,
			final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mFactory = factory;
		mLogger = logger;
		mMgdScript = script;
		mSymbolTable = symbolTable;
		mTruePredicate = truePredicate;
		mFalsePredicate = falsePredicate;
		mRoot = null;
	}

	private Deque<Map<Term, Term>> findRPath(final T pred) {
		final Deque<Map<Term, Term>> path = new HashDeque<>();

		IVertex current = mRoot;
		ModelVertex parent = null;
		// find the predicate with the same fulfilling models
		while (current instanceof ModelVertex) {
			parent = (ModelVertex) current;
			final boolean edge = fulfillsPredicate(pred, parent.getWitness());
			current = parent.getChild(edge);
			path.add(parent.getWitness());
		}
		mLogger.info("predicate at end of path: " + current);
		return path;
	}

	private Deque<Map<Term, Term>> findRealPath(final T pred) {
		ArrayDeque<ModelVertex> path = new ArrayDeque<>();
		path.addFirst((ModelVertex) mRoot);
		final ArrayDeque<ModelVertex> pathT = findPathHelper(pred, true, path.clone());
		final ArrayDeque<ModelVertex> pathF = findPathHelper(pred, false, path.clone());
		if (pathT.size() > pathF.size()) {
			path = pathT;
		} else {
			path = pathF;
		}
		mLogger.info("predicate at end of path true: " + path.getLast().getChild(true));
		mLogger.info("predicate at end of path false: " + path.getLast().getChild(false));
		final ArrayDeque<Map<Term, Term>> result = new ArrayDeque<>();
		while (!path.isEmpty()) {
			result.addLast(path.removeFirst().getWitness());
		}
		return result;
	}

	private ArrayDeque<ModelVertex> findPathHelper(final T pred, final boolean turn,
			final ArrayDeque<ModelVertex> path) {
		final IVertex end = path.getLast().getChild(turn);
		if (end instanceof PredicateVertex) {
			if (((PredicateVertex<?>) end).mPredicate.equals(pred)) {
				return path;
			}
			return new ArrayDeque<>();
		}
		path.addLast((ModelVertex) end);
		final ArrayDeque<ModelVertex> pathT = findPathHelper(pred, true, path.clone());
		final ArrayDeque<ModelVertex> pathF = findPathHelper(pred, false, path.clone());
		if (pathT.size() > pathF.size()) {
			return pathT;
		}
		return pathF;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		stringHelper(mRoot, sb);
		return sb.toString();
	}

	private void stringHelper(final IVertex vertex, final StringBuilder sb) {
		if (vertex instanceof ModelVertex) {
			sb.append(vertex.print() + "\n");
			stringHelper(((ModelVertex) vertex).getChild(true), sb);
			stringHelper(((ModelVertex) vertex).getChild(false), sb);
		}
	}

	/**
	 * @returns the equivalent predicate, if there is no such predicate the given one is added and returned
	 */
	protected T unifyPredicate(final T predicate) {
		// empty tree
		if (mRoot == null) {
			mRoot = new PredicateVertex<>(predicate);
			// final Term term = SmtUtils.simplify(mMgdScript, predicate.getFormula(), mServices,
			// SimplificationTechnique.SIMPLIFY_DDA);
			// final Term commuNF = new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(term);
			// final T newPred = (T) mFactory.newPredicate(commuNF);
			mPredicates.add(predicate);
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
		// ______________
		for (final T p : mPredicates) {
			final Term a = p.getClosedFormula();
			final Term b = predicate.getClosedFormula();
			if (mMgdScript.isLocked()) {
				mMgdScript.requestLockRelease();
			}
			mMgdScript.lock(this);
			mMgdScript.push(this, 1);
			final Term isEqual = mMgdScript.term(this, "distinct", a, b);
			try {
				mMgdScript.assertTerm(this, isEqual);
				final LBool result = mMgdScript.checkSat(this);
				if (result == LBool.UNSAT) {
					mLogger.info("new: " + predicate);
					mLogger.info("newPath: " + findRPath(predicate));
					mLogger.info("old: " + p);
					mLogger.info("newPath: " + findRealPath(p));
					throw new UnsupportedOperationException("EQUALITY NOT FOUND" + mPredicates.size());
				}
			} finally {
				mMgdScript.pop(this, 1);
				mMgdScript.unlock(this);
			}
		}
		// ______________
		// the given predicate is new and inserted to the tree
		final ModelVertex newNode = fulfillsPredicate(predicate, newWitness)
				? new ModelVertex(new PredicateVertex<>(predicate), current, newWitness)
				: new ModelVertex(current, new PredicateVertex<>(predicate), newWitness);
		if (parent != null) {
			parent.swapChild(current, newNode);
		} else {
			mRoot = newNode;
		}
		// final Term term = SmtUtils.simplify(mMgdScript, predicate.getFormula(), mServices,
		// SimplificationTechnique.SIMPLIFY_DDA);
		// final Term commuNF = new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(term);
		// final T newPred = (T) mFactory.newPredicate(commuNF);
		mPredicates.add(predicate);
		return predicate;
	}

	/**
	 * check if model fulfills predicate
	 */
	protected boolean fulfillsPredicate(final T predicate, final Map<Term, Term> witness) {
		final SubstitutionWithLocalSimplification subst = new SubstitutionWithLocalSimplification(mMgdScript, witness);
		final Term result = subst.transform(predicate.getClosedFormula());

		if (mTruePredicate.getFormula().equals(result)) {
			return true;
		}
		assert checkFalseCase(predicate, witness, result) : "unexpected false case";
		return false;
	}

	private boolean checkFalseCase(final T predicate, final Map<Term, Term> witness, final Term result) {
		if (mFalsePredicate.getFormula().equals(result)) {
			return true;
		}
		final Term trueTerm = mTruePredicate.getClosedFormula();
		final Term query = mMgdScript.getScript().term("distinct", trueTerm, result);
		final LBool isNotTrue = SmtUtils.checkSatTerm(mMgdScript.getScript(), query);
		if (isNotTrue == LBool.UNSAT) {
			mLogger.fatal("Simplification failed: it is actually equal to true");
			mLogger.fatal(query.toStringDirect());
			mLogger.fatal("original predicate: " + predicate.toString());
			mLogger.fatal("witness           : " + witness.toString());
			return false;
		}
		return true;
	}

	/**
	 * check if predicates are equal
	 */
	private Map<Term, Term> compare(final T predicate, final T leafPredicate) {
		final T localPred = leafPredicate;
		final Term local = localPred.getClosedFormula();
		final Term other = predicate.getClosedFormula();
		// TODO replace with getWitness()
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		final Term isEqual = mMgdScript.term(this, "distinct", local, other);
		try {
			mMgdScript.assertTerm(this, isEqual);
			final LBool result = mMgdScript.checkSat(this);
			if (result == LBool.UNSAT) {
				// they are equal
				return Collections.emptyMap();
			} else if (result == LBool.SAT) {
				// they are not equal
				final Set<ApplicationTerm> terms = mSymbolTable.computeAllDefaultConstants();
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

	// -- functions for restructure --

	protected Map<Term, Term> getWitness(final Term term) {
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
			}
			throw new UnsupportedOperationException("Solver cannot find a model for the term " + term);
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
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

	public PredicateTrie<T> fillTrie(final RestructureHelperObject root,
			final Map<RestructureHelperObject, Pair<RestructureHelperObject, RestructureHelperObject>> witnessMap) {
		if (mRoot != null) {
			throw new UnsupportedOperationException("trie must be empty");
		}

		final Map<RestructureHelperObject, ModelVertex> modelVertices = new HashMap<>();

		for (final RestructureHelperObject key : witnessMap.keySet()) {
			modelVertices.put(key, new ModelVertex(null, null, key.getWitness()));
		}
		for (final Map.Entry<RestructureHelperObject, Pair<RestructureHelperObject, RestructureHelperObject>> entry : witnessMap
				.entrySet()) {
			final Pair<RestructureHelperObject, RestructureHelperObject> children = entry.getValue();
			if (children.getFirst().getSerialNumber() == -1) {
				// predicate
				final IVertex trueChild = new PredicateVertex<>(children.getFirst().getPredicate());
				modelVertices.get(entry.getKey()).setTrueChild(trueChild);
			} else {
				// model
				modelVertices.get(entry.getKey()).setTrueChild(modelVertices.get(children.getFirst()));
			}
			if (children.getSecond().getSerialNumber() == -1) {
				// predicate
				final IVertex falseChild = new PredicateVertex<>(children.getSecond().getPredicate());
				modelVertices.get(entry.getKey()).setFalseChild(falseChild);
			} else {
				// model
				modelVertices.get(entry.getKey()).setFalseChild(modelVertices.get(children.getSecond()));
			}
		}
		mRoot = modelVertices.get(root);
		return this;
	}
}