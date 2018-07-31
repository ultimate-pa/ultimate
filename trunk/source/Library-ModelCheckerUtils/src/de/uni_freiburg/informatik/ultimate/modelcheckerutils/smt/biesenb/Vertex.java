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
import java.util.HashSet;
import java.util.Set;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class Vertex<T> {
	private final T mPredicate;
	private final Set<Vertex<T>> mChildren;
	private final Set<Vertex<T>> mParents;

	public Vertex(final T predicate, final Set<Vertex<T>> children, final Set<Vertex<T>> parents) {
		mPredicate = predicate;
		mChildren = children;
		mParents = parents;
	}

	public void updateEdges() {
		for (final Vertex<T> parent : mParents) {
			for (final Vertex<T> child : mChildren) {
				if (parent.mChildren.contains(child)) {
					parent.removeChild(child);
					child.removeParent(parent);
				}
				child.addParent(this);
			}
			parent.addChild(this);
		}
	}

	public int getImplicationCount(final boolean implying) {
		int a = implying ? 0 : 1;
		final Set<Vertex<T>> marked = new HashSet<>();
		final Deque<Vertex<T>> parents = new ArrayDeque<>(mParents);
		while (!parents.isEmpty()) {
			final Vertex<T> current = parents.pop();
			if (!marked.add(current)) {
				continue;
			}
			++a;
			parents.addAll(current.getParents());
		}
		int b = implying ? 1 : 0;
		marked.clear();
		final Deque<Vertex<T>> children = new ArrayDeque<>(mChildren);
		while (!children.isEmpty()) {
			final Vertex<T> current = children.pop();
			if (!marked.add(current)) {
				continue;
			}
			++b;
			children.addAll(current.getChildren());
		}
		return a * b / (a + b) + 1;
	}

	@Override
	public String toString() {
		final Deque<T> c = new ArrayDeque<>();
		mChildren.forEach(child -> c.add(child.mPredicate));
		return String.valueOf(mPredicate.toString()) + "-> " + c.toString();
	}

	public Set<Vertex<T>> getChildren() {
		return mChildren;
	}

	public Set<Vertex<T>> getParents() {
		return mParents;
	}

	public boolean addChild(final Vertex<T> child) {
		return mChildren.add(child);
	}

	public boolean addParent(final Vertex<T> parent) {
		return mParents.add(parent);
	}

	public boolean removeChild(final Vertex<T> child) {
		return mChildren.remove(child);
	}

	public boolean removeParent(final Vertex<T> parent) {
		return mParents.remove(parent);
	}

	public T getPredicate() {
		return mPredicate;
	}

	public Set<Vertex<T>> getDescendants() {
		final Set<Vertex<T>> decendants = new HashSet<>(mChildren);
		final Deque<Vertex<T>> vertex = new ArrayDeque<>(mChildren);
		while (!vertex.isEmpty()) {
			final Vertex<T> current = vertex.removeFirst();
			decendants.addAll(current.mChildren);
			vertex.addAll(current.mChildren);
		}
		return decendants;
	}
}