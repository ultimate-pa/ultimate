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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ImplicationGraph<T extends IPredicate> {
	private final ManagedScript mScript;
	private final Set<Vertex<T>> mVertices;
	private final Vertex<T> mVertexTrue;
	private final Vertex<T> mVertexFalse;

	public ImplicationGraph(final ManagedScript script, final T predicateFalse, final T predicateTrue) {
		mScript = script;
		mVertices = new HashSet<>();
		mVertexFalse = new Vertex<>(predicateFalse, new HashSet<>(), new HashSet<>());
		mVertexTrue = new Vertex<>(predicateTrue, new HashSet<>(), new HashSet<>());
		mVertexFalse.addChild(mVertexTrue);
		mVertexTrue.addParent(mVertexFalse);
		mVertices.add(mVertexTrue);
		mVertices.add(mVertexFalse);
	}

	@Override
	public String toString() {
		final StringBuilder bld = new StringBuilder();
		for (final Vertex<T> vertex : mVertices) {
			bld.append("\n " + vertex.toString());
		}
		return bld.toString();
	}

	public Vertex<T> unifyPredicate(final T predicate) {
		int max;
		boolean implying = true;
		final Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> copy = createFullCopy();
		final Set<Vertex<T>> marked = new HashSet<>();
		Vertex<T> maxVertex = null;
		// find the predicates that imply the given predicate
		while (!marked.containsAll(copy.getFirst().mVertices)) {
			max = 0;
			maxVertex = null;
			for (final Vertex<T> vertex : copy.getFirst().mVertices) {
				int count;
				if (marked.contains(vertex) || (count = vertex.getImplicationCount(implying)) <= max) {
					continue;
				}
				max = count;
				maxVertex = vertex;
			}
			// TODO can't be null
			if (implication(maxVertex.getPredicate(), predicate)) {
				marked.add(maxVertex);
				copy.getFirst().removeAllVerticesImplying(maxVertex);
				continue;
			}
			copy.getFirst().removeAllImpliedVertices(maxVertex);
			for (final Vertex<T> v2 : maxVertex.getParents()) {
				v2.removeChild(maxVertex);
			}
			copy.getFirst().mVertices.remove(maxVertex);
		}
		final Set<Vertex<T>> parents = new HashSet<>();
		copy.getFirst().mVertices.forEach(v -> parents.add(copy.getSecond().get(v)));
		implying = false;
		final Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> subCopy = createSubCopy(parents);
		marked.clear();
		// find the predicates that are implied by the given predicate
		while (!marked.containsAll(subCopy.getFirst().mVertices)) {
			max = 0;
			maxVertex = null;
			for (final Vertex<T> vertex : subCopy.getFirst().mVertices) {
				int count;
				if (marked.contains(vertex) || (count = vertex.getImplicationCount(implying)) <= max) {
					continue;
				}
				max = count;
				maxVertex = vertex;
			}
			// TODO can't be null
			if (implication(predicate, maxVertex.getPredicate())) {
				marked.add(maxVertex);
				subCopy.getFirst().removeAllImpliedVertices(maxVertex);
				continue;
			}
			subCopy.getFirst().removeAllVerticesImplying(maxVertex);
			for (final Vertex<T> v3 : maxVertex.getParents()) {
				v3.removeChild(maxVertex);
			}
			subCopy.getFirst().mVertices.remove(maxVertex);
		}
		final HashSet<Vertex<T>> children = new HashSet<>();
		subCopy.getFirst().mVertices.forEach(v -> children.add(subCopy.getSecond().get(v)));
		final Vertex<T> newVertex = new Vertex<>(predicate, children, parents);
		newVertex.updateEdges();
		mVertices.add(newVertex);
		return newVertex;
	}

	private boolean removeAllImpliedVertices(final Vertex<T> vertex) {
		if (!mVertices.contains(vertex)) {
			return false;
		}
		final Deque<Vertex<T>> children = new ArrayDeque<>(vertex.getChildren());
		while (!children.isEmpty()) {
			final Vertex<T> current = children.pop();
			if (!mVertices.remove(current)) {
				continue;
			}
			current.getParents().forEach(v -> v.removeChild(current));
			children.addAll(current.getChildren());
		}
		return true;
	}

	private boolean removeAllVerticesImplying(final Vertex<T> vertex) {
		if (!mVertices.contains(vertex)) {
			return false;
		}
		final Deque<Vertex<T>> parents = new ArrayDeque<>(vertex.getParents());
		while (!parents.isEmpty()) {
			final Vertex<T> current = parents.pop();
			if (!mVertices.remove(current)) {
				continue;
			}
			current.getChildren().forEach(v -> v.removeParent(current));
			parents.addAll(current.getParents());
		}
		return true;
	}

	private boolean implication(final T a, final T b) {
		final Term acf = a.getClosedFormula();
		final Term bcf = b.getClosedFormula();
		mScript.lock(this);
		final Term imp = mScript.term(this, "and", acf, mScript.term(this, "not", bcf));
		mScript.push(this, 1);
		try {
			mScript.assertTerm(this, imp);
			final Script.LBool result = mScript.checkSat(this);
			if (result == Script.LBool.UNSAT) {
				return true;
			}
			if (result == Script.LBool.SAT) {
				return false;
			}
			throw new UnsupportedOperationException(
					"Cannot handle case were solver cannot decide implication of predicates");
		} finally {
			mScript.pop(this, 1);
			mScript.unlock(this);
		}
	}

	private Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> createFullCopy() {
		final ImplicationGraph<T> copy =
				new ImplicationGraph<>(mScript, mVertexTrue.getPredicate(), mVertexFalse.getPredicate());
		copy.mVertices.clear();
		final Map<Vertex<T>, Vertex<T>> vertexCopyMap = new HashMap<>();
		for (final Vertex<T> vertex : mVertices) {
			vertexCopyMap.put(vertex, new Vertex<>(vertex.getPredicate(), new HashSet<>(), new HashSet<>()));
		}
		for (final Vertex<T> vertex : mVertices) {
			final Vertex<T> vertexCopy = vertexCopyMap.get(vertex);
			for (final Vertex<T> child : vertex.getChildren()) {
				vertexCopy.addChild(vertexCopyMap.get(child));
			}
			for (final Vertex<T> parent : vertex.getParents()) {
				vertexCopy.addParent(vertexCopyMap.get(parent));
			}
			copy.mVertices.add(vertexCopy);
		}
		final Map<Vertex<T>, Vertex<T>> invertedMap = new HashMap<>();
		for (final Map.Entry<Vertex<T>, Vertex<T>> entry : vertexCopyMap.entrySet()) {
			invertedMap.put(entry.getValue(), entry.getKey());
		}
		return new Pair<>(copy, invertedMap);
	}

	private Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> createSubCopy(final Set<Vertex<T>> parents) {
		final ImplicationGraph<T> copy =
				new ImplicationGraph<>(mScript, mVertexTrue.getPredicate(), mVertexFalse.getPredicate());
		copy.mVertices.clear();
		final Set<Vertex<T>> subVertices = parents.iterator().next().getDescendants();
		for (final Vertex<T> init : parents) {
			final Set<Vertex<T>> toRemove = new HashSet<>();
			for (final Vertex<T> vertex : subVertices) {
				if (init.getDescendants().contains(vertex)) {
					continue;
				}
				toRemove.add(vertex);
			}
			subVertices.removeAll(toRemove);
		}
		final HashMap<Vertex<T>, Vertex<T>> vertexCopyMap = new HashMap<>();
		for (final Vertex<T> vertex : subVertices) {
			vertexCopyMap.put(vertex, new Vertex<>(vertex.getPredicate(), new HashSet<>(), new HashSet<>()));
		}
		for (final Vertex<T> vertex : subVertices) {
			final Vertex<T> vertexCopy = vertexCopyMap.get(vertex);
			for (final Vertex<T> child : vertex.getChildren()) {
				if (!subVertices.contains(child)) {
					continue;
				}
				vertexCopy.addChild(vertexCopyMap.get(child));
			}
			for (final Vertex<T> parent : vertex.getParents()) {
				if (!subVertices.contains(parent)) {
					continue;
				}
				vertexCopy.addParent(vertexCopyMap.get(parent));
			}
			copy.mVertices.add(vertexCopy);
		}
		final Map<Vertex<T>, Vertex<T>> invertedMap = new HashMap<>();
		for (final Map.Entry<Vertex<T>, Vertex<T>> entry : vertexCopyMap.entrySet()) {
			invertedMap.put(entry.getValue(), entry.getKey());
		}
		return new Pair<>(copy, invertedMap);
	}
}
