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
import java.util.HashSet;
import java.util.Set;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class Vertex<T> {
    public final T mPredicate;
    private Set<Vertex<T>> mChildren;
    private Set<Vertex<T>> mParents;

    public Vertex(T predicate, Set<Vertex<T>> children, Set<Vertex<T>> parents) {
        this.mPredicate = predicate;
        this.mChildren = children;
        this.mParents = parents;
    }

    public void updateEdges() {
        for (Vertex<T> parent : this.mParents) {
            for (Vertex<T> child : this.mChildren) {
                if (parent.mChildren.contains(child)) {
                    parent.removeChild(child);
                    child.removeParent(parent);
                }
                child.addParent(this);
            }
            parent.addChild(this);
        }
    }

    public int getImplicationCount(boolean implying) {
        int a = implying ? 0 : 1;
        HashSet<Vertex<T>> marked = new HashSet<Vertex<T>>();
        ArrayDeque<Vertex<T>> parents = new ArrayDeque<Vertex<T>>(this.mParents);
        while (!parents.isEmpty()) {
            Vertex<T> current = parents.pop();
            if (!marked.add(current)) continue;
            ++a;
            parents.addAll(current.getParents());
        }
        int b = implying ? 1 : 0;
        marked.clear();
        ArrayDeque<Vertex<T>> children = new ArrayDeque<Vertex<T>>(this.mChildren);
        while (!children.isEmpty()) {
            Vertex<T> current = children.pop();
            if (!marked.add(current)) continue;
            ++b;
            children.addAll(current.getChildren());
        }
        return a * b / (a + b) + 1;
    }

    public String toString() {
        ArrayDeque c = new ArrayDeque();
        this.mChildren.forEach(child -> {
            boolean bl = c.add(child.mPredicate);
        }
        );
        return String.valueOf(this.mPredicate.toString()) + "-> " + c.toString();
    }

    public Set<Vertex<T>> getChildren() {
        return this.mChildren;
    }

    public Set<Vertex<T>> getParents() {
        return this.mParents;
    }

    public boolean addChild(Vertex<T> child) {
        return this.mChildren.add(child);
    }

    public boolean addParent(Vertex<T> parent) {
        return this.mParents.add(parent);
    }

    public boolean removeChild(Vertex<T> child) {
        return this.mChildren.remove(child);
    }

    public boolean removeParent(Vertex<T> parent) {
        return this.mParents.remove(parent);
    }

    public Set<Vertex<T>> getDescendants() {
        HashSet<Vertex<T>> decendants = new HashSet<Vertex<T>>(this.mChildren);
        ArrayDeque<Vertex<T>> vertex = new ArrayDeque<Vertex<T>>(this.mChildren);
        while (!vertex.isEmpty()) {
            Vertex<T> current = vertex.removeFirst();
            decendants.addAll(current.mChildren);
            vertex.addAll(current.mChildren);
        }
        return decendants;
    }
}