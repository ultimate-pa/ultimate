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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Data structure that stores predicates and there implication-relation. A predicate implies its descendants and is
 * implied by its ancestors.
 *
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ImplicationGraph<T extends IPredicate> {
	private final ManagedScript mMgdScript;
	private final Set<ImplicationVertex<T>> mVertices;
	private final Map<T, ImplicationVertex<T>> mPredicateMap;
	private ImplicationVertex<T> mTrueVertex;
	private ImplicationVertex<T> mFalseVertex;

	protected ImplicationGraph(final ManagedScript script, final T predicateFalse, final T predicateTrue) {
		mMgdScript = script;
		mVertices = new HashSet<>();
		mPredicateMap = new HashMap<>();
		mFalseVertex = new ImplicationVertex<>(predicateFalse, new HashSet<>(), new HashSet<>());
		Set<ImplicationVertex<T>> parent = new HashSet<>();
		parent.add(mFalseVertex);
		mTrueVertex = new ImplicationVertex<>(predicateTrue, new HashSet<>(), parent);
		mFalseVertex.addChild(mTrueVertex);

		mVertices.add(mTrueVertex);
		mVertices.add(mFalseVertex);
		mPredicateMap.put(predicateTrue, mTrueVertex);
		mPredicateMap.put(predicateFalse, mFalseVertex);
	}

	protected ImplicationVertex<T> getTrueVertex() {
		return mTrueVertex;
	}

	protected ImplicationVertex<T> getFalseVertex() {
		return mFalseVertex;
	}

	protected ImplicationVertex<T> getVertex(final T pred) {
		final ImplicationVertex<T> rtr = mPredicateMap.get(pred);
		if (rtr == null) {
			throw new IllegalArgumentException("predicate " + pred + " is unknown");
		}
		return rtr;
	}

	protected Set<ImplicationVertex<T>> getVertices() {
		return mVertices;
	}

	@Override
	public String toString() {
		final StringBuilder bld = new StringBuilder();
		for (final ImplicationVertex<T> vertex : mVertices) {
			bld.append("\n " + vertex.toString());
		}
		return bld.toString();
	}

	/**
	 * Insert a predicate into the implication graph
	 *
	 * @param predicate
	 * @return the implication-vertex it is stored in
	 */
	protected ImplicationVertex<T> unifyPredicate(final T predicate) {
		TransitiveClosureIG<T> transitiveClosure = new TransitiveClosureIG<>(this);
		final Set<ImplicationVertex<T>> marked = new HashSet<>();
		// find the predicates that imply the given predicate
		while (!marked.containsAll(transitiveClosure.getVertices())) {
			// find predicate with highest count
			ImplicationVertex<T> maxVertex = transitiveClosure.getMaxTransitiveClosureCount(marked, true);
			if (internImplication(maxVertex.getPredicate(), predicate, true)) {
				marked.add(maxVertex);
				transitiveClosure.removeAncestorsFromTC(maxVertex);
			}else {
				transitiveClosure.removeDescendantsFromTC(maxVertex);
				transitiveClosure.removeVertex(maxVertex);
			}
		}
		final Set<ImplicationVertex<T>> parents = new HashSet<>(transitiveClosure.getVertices());
		// find the predicates that are implied by the given predicate

		transitiveClosure = new TransitiveClosureIG<>(this, parents);
		marked.clear();
		while (!marked.containsAll(transitiveClosure.getVertices())) {
			ImplicationVertex<T> maxVertex = transitiveClosure.getMaxTransitiveClosureCount(marked, false);
			if (internImplication(predicate, maxVertex.getPredicate(), true)) {
				marked.add(maxVertex);
				transitiveClosure.removeDescendantsFromTC(maxVertex);
			} else {
				transitiveClosure.removeAncestorsFromTC(maxVertex);
				transitiveClosure.removeVertex(maxVertex);
			}
		}
		final HashSet<ImplicationVertex<T>> children = new HashSet<>(transitiveClosure.getVertices());
		final ImplicationVertex<T> newVertex = new ImplicationVertex<>(predicate, children, parents);
		mVertices.add(newVertex);
		mPredicateMap.put(predicate, newVertex);
		return newVertex;
	}

	/**
	 * removes all predicates form the collection, that are implied within the collection
	 */
	protected Collection<T> removeImpliedVerticesFromCollection(final Collection<T> collection) {
		HashSet<ImplicationVertex<T>> vertexCollection = new HashSet<>();
		collection.forEach(c -> vertexCollection.add(mPredicateMap.get(c)));
		Collection<T> result = new HashSet<>(collection);
		for(ImplicationVertex<T> c1 : vertexCollection) {
			for(ImplicationVertex<T> c2 : vertexCollection) {
				if(c1.getAncestors().contains(c2)) {
					result.remove(c1.getPredicate());
					break;
				}
			}
		}
		return result;
	}
	
	/**
	 * removes all predicates form the collection, that imply other predicates in the collection
	 */
	public Collection<T> removeImplyingVerticesFromCollection(final Collection<T> collection) {
		HashSet<ImplicationVertex<T>> vertexCollection = new HashSet<>();
		collection.forEach(c -> vertexCollection.add(mPredicateMap.get(c)));
		Collection<T> result = new HashSet<>(collection);
		for(ImplicationVertex<T> c1 : vertexCollection) {
			for(ImplicationVertex<T> c2 : vertexCollection) {
				if(c1.getDescendants().contains(c2)) {
					result.remove(c1.getPredicate());
					break;
				}
			}
		}
		return result;
	}

	/**
	 * checks for implication - if the predicates are known, the graph is used
	 *
	 * @return true if a implies b
	 */
	protected boolean implication(final T a, final T b) {
		return internImplication(a, b, false);
	}

	protected boolean internImplication(final T a, final T b, final boolean useSolver) {
		if (a.equals(b)) {
			return true;
		}
		if (mPredicateMap.containsKey(a) && mPredicateMap.containsKey(b)) {
			return getVertex(a).getDescendants().contains(getVertex(b));
		}
		if (useSolver) {
			final Term acf = a.getClosedFormula();
			final Term bcf = b.getClosedFormula();
			if (mMgdScript.isLocked()) {
				mMgdScript.requestLockRelease();
			}
			mMgdScript.lock(this);
			final Term imp = mMgdScript.term(this, "and", acf, mMgdScript.term(this, "not", bcf));
			mMgdScript.push(this, 1);
			try {
				mMgdScript.assertTerm(this, imp);
				final Script.LBool result = mMgdScript.checkSat(this);
				if (result == Script.LBool.UNSAT) {
					return true;
				}
				if (result == Script.LBool.SAT) {
					return false;
				}
				throw new UnsupportedOperationException(
						"Cannot handle case were solver cannot decide implication of predicates");
			} finally {
				mMgdScript.pop(this, 1);
				mMgdScript.unlock(this);
			}
		}
		throw new IllegalArgumentException("predicate is not known, use the solver-option");
	}
}
