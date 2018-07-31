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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb.Vertex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ImplicationGraph<T extends IPredicate> {
    private ManagedScript mScript;
    private Set<Vertex<T>> mVertices;
    private Vertex<T> mVertexTrue;
    private Vertex<T> mVertexFalse;

    public ImplicationGraph(ManagedScript script, T predicateFalse, T predicateTrue) {
        mScript = script;
        mVertices = new HashSet<>();
        mVertexFalse = new Vertex<>(predicateFalse, new HashSet<>(), new HashSet<>());
        mVertexTrue = new Vertex<>(predicateTrue, new HashSet<>(), new HashSet<>());
        mVertexFalse.addChild(this.mVertexTrue);
        mVertexTrue.addParent(this.mVertexFalse);
        mVertices.add(this.mVertexTrue);
        mVertices.add(this.mVertexFalse);
    }

    public String toString() {
        StringBuilder bld = new StringBuilder();
        for (Vertex<T> vertex : this.mVertices) {
            bld.append("\n " + vertex.toString());
        }
        return bld.toString();
    }

    public Vertex<T> unifyPredicate(T predicate) {
        int max;
        boolean implying = true;
        Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> copy = this.createFullCopy();
        Set<Vertex<T>> marked = new HashSet<>();
        Vertex<T> maxVertex = null;
        // find the predicates that imply the given predicate
        while (!marked.containsAll(copy.getFirst().mVertices)) {
            max = 0;
            maxVertex = null;
            for (Vertex<T> vertex : copy.getFirst().mVertices) {
                int count;
                if (marked.contains(vertex) || (count = vertex.getImplicationCount(implying)) <= max) continue;
                max = count;
                maxVertex = vertex;
            }
            // TODO can't be null
            if (implication(maxVertex.mPredicate, predicate)) {
                marked.add(maxVertex);
                copy.getFirst().removeAllVerticesImplying(maxVertex);
                continue;
            }
            copy.getFirst().removeAllImpliedVertices(maxVertex);
            for (Vertex<T> v2 : maxVertex.getParents()) {
                v2.removeChild(maxVertex);
            }
            copy.getFirst().mVertices.remove(maxVertex);
        }
        Set<Vertex<T>> parents = new HashSet<>();
        copy.getFirst().mVertices.forEach(v -> parents.add(copy.getSecond().get(v)));
        implying = false;
        Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> subCopy = this.createSubCopy(parents);
        marked.clear();
        // find the predicates that are implied by the given predicate
        while (!marked.containsAll(subCopy.getFirst().mVertices)) {
            max = 0;
            maxVertex = null;
            for (Vertex<T> vertex : subCopy.getFirst().mVertices) {
                int count;
                if (marked.contains(vertex) || (count = vertex.getImplicationCount(implying)) <= max) continue;
                max = count;
                maxVertex = vertex;
            }
            // TODO can't be null
            if (implication(predicate, maxVertex.mPredicate)) {
                marked.add(maxVertex);
                subCopy.getFirst().removeAllImpliedVertices(maxVertex);
                continue;
            }
            subCopy.getFirst().removeAllVerticesImplying(maxVertex);
            for (Vertex<T> v3 : maxVertex.getParents()) {
                v3.removeChild(maxVertex);
            }
            subCopy.getFirst().mVertices.remove(maxVertex);
        }
        HashSet<Vertex<T>> children = new HashSet<>();
        subCopy.getFirst().mVertices.forEach(v -> children.add(subCopy.getSecond().get(v)));
        Vertex<T> newVertex = new Vertex<>(predicate, children, parents);
        newVertex.updateEdges();
        this.mVertices.add(newVertex);
        return newVertex;
    }

    private boolean removeAllImpliedVertices(Vertex<T> vertex) {
        if (!this.mVertices.contains(vertex)) {
            return false;
        }
        Deque<Vertex<T>> children = new ArrayDeque<>(vertex.getChildren());
        while (!children.isEmpty()) {
            Vertex<T> current = children.pop();
            if (!this.mVertices.remove(current)) continue;
            current.getParents().forEach(v -> v.removeChild(current));
            children.addAll(current.getChildren());
        }
        return true;
    }

    private boolean removeAllVerticesImplying(Vertex<T> vertex) {
        if (!this.mVertices.contains(vertex)) {
            return false;
        }
        Deque<Vertex<T>> parents = new ArrayDeque<>(vertex.getParents());
        while (!parents.isEmpty()) {
            Vertex<T> current = parents.pop();
            if (!this.mVertices.remove(current)) continue;
            current.getChildren().forEach(v -> v.removeParent(current));
            parents.addAll(current.getParents());
        }
        return true;
    }

    private boolean implication(T a, T b) {
        Term acf = a.getClosedFormula();
        Term bcf = b.getClosedFormula();
        this.mScript.lock((Object)this);
        Term imp = mScript.term(this, "and", acf, mScript.term(this, "not", bcf));
        this.mScript.push((Object)this, 1);
        try {
            this.mScript.assertTerm(this, imp);
            Script.LBool result = this.mScript.checkSat((Object)this);
            if (result == Script.LBool.UNSAT) {
                return true;
            }
            if (result == Script.LBool.SAT) {
                return false;
            }
            throw new UnsupportedOperationException("Cannot handle case were solver cannot decide implication of predicates");
        }
        finally {
            this.mScript.pop((Object)this, 1);
            this.mScript.unlock((Object)this);
        }
    }

    private Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> createFullCopy() {
        ImplicationGraph<T> copy = new ImplicationGraph<>(mScript, mVertexTrue.mPredicate, mVertexFalse.mPredicate);
        copy.mVertices.clear();
        Map<Vertex<T>, Vertex<T>> vertexCopyMap = new HashMap<>();
        for (Vertex<T> vertex :mVertices) {
            vertexCopyMap.put(vertex, new Vertex<T>(vertex.mPredicate, new HashSet<>(), new HashSet<>()));
        }
        for (Vertex<T> vertex : mVertices) {
            Vertex<T> vertexCopy = vertexCopyMap.get(vertex);
            for (Vertex<T> child : vertex.getChildren()) {
                vertexCopy.addChild(vertexCopyMap.get(child));
            }
            for (Vertex<T> parent : vertex.getParents()) {
                vertexCopy.addParent(vertexCopyMap.get(parent));
            }
            copy.mVertices.add(vertexCopy);
        }
        Map<Vertex<T>, Vertex<T>> invertedMap = new HashMap<>();
        for (Map.Entry<Vertex<T>, Vertex<T>> entry : vertexCopyMap.entrySet()) {
            invertedMap.put(entry.getValue(), entry.getKey());
        }
        return new Pair<>(copy, invertedMap);
    }

    private Pair<ImplicationGraph<T>, Map<Vertex<T>, Vertex<T>>> createSubCopy(Set<Vertex<T>> parents) {
        ImplicationGraph<T> copy = new ImplicationGraph<>(mScript, mVertexTrue.mPredicate, mVertexFalse.mPredicate);
        copy.mVertices.clear();
        Set<Vertex<T>> subVertices = parents.iterator().next().getDescendants();
        for (Vertex<T> init : parents) {
            Set<Vertex<T>> toRemove = new HashSet<>();
            for (Vertex<T> vertex : subVertices) {
                if (init.getDescendants().contains(vertex)) continue;
                toRemove.add(vertex);
            }
            subVertices.removeAll(toRemove);
        }
        HashMap<Vertex<T>, Vertex<T>> vertexCopyMap = new HashMap<>();
        for (Vertex<T> vertex : subVertices) {
            vertexCopyMap.put(vertex, new Vertex<>(vertex.mPredicate, new HashSet<>(), new HashSet<>()));
        }
        for (Vertex<T> vertex : subVertices) {
            Vertex<T> vertexCopy = vertexCopyMap.get(vertex);
            for (Vertex<T> child : vertex.getChildren()) {
                if (!subVertices.contains(child)) continue;
                vertexCopy.addChild(vertexCopyMap.get(child));
            }
            for (Vertex<T> parent : vertex.getParents()) {
                if (!subVertices.contains(parent)) continue;
                vertexCopy.addParent(vertexCopyMap.get(parent));
            }
            copy.mVertices.add(vertexCopy);
        }
        Map<Vertex<T>, Vertex<T>> invertedMap = new HashMap<>();
        for (Map.Entry<Vertex<T>, Vertex<T>> entry : vertexCopyMap.entrySet()) {
            invertedMap.put(entry.getValue(), entry.getKey());
        }
        return new Pair<>(copy, invertedMap);
    }
}
