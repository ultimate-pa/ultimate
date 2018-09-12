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
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

/**
 * The implication vertex is part of the @ImplicationGraph.java and stores a predicate
 * Descendants are implied predicates and ancestors imply the predicate.
 * 
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ImplicationVertex<T> {
	private final T mPredicate;
	private final Set<ImplicationVertex<T>> mChildren;
	private final Set<ImplicationVertex<T>> mParents;

	public ImplicationVertex(final T predicate, final Set<ImplicationVertex<T>> children, final Set<ImplicationVertex<T>> parents) {
		mPredicate = predicate;
		mChildren = children;
		mParents = parents;
	}

	/**
	 * remove edges due to transitive reduction
	 */
	protected void updateEdges() {
		for (final ImplicationVertex<T> parent : mParents) {
			for (final ImplicationVertex<T> child : mChildren) {
				if (parent.mChildren.contains(child)) {
					parent.removeChild(child);
					child.removeParent(parent);
				}
				child.addParent(this);
			}
			parent.addChild(this);
		}
	}

	/**
	 * Calculates a count to go through the implication graph more efficient
	 */
	protected int getImplicationCount(final boolean implying) {
		int a = implying ? 0 : 1;
		final Set<ImplicationVertex<T>> marked = new HashSet<>();
		final Deque<ImplicationVertex<T>> parents = new ArrayDeque<>(mParents);
		while (!parents.isEmpty()) {
			final ImplicationVertex<T> current = parents.pop();
			if (!marked.add(current)) {
				continue;
			}
			++a;
			parents.addAll(current.getParents());
		}
		int b = implying ? 1 : 0;
		marked.clear();
		final Deque<ImplicationVertex<T>> children = new ArrayDeque<>(mChildren);
		while (!children.isEmpty()) {
			final ImplicationVertex<T> current = children.pop();
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

	protected Set<ImplicationVertex<T>> getChildren() {
		return mChildren;
	}

	protected Set<ImplicationVertex<T>> getParents() {
		return mParents;
	}

	protected boolean addChild(final ImplicationVertex<T> child) {
		return mChildren.add(child);
	}

	protected boolean addParent(final ImplicationVertex<T> parent) {
		return mParents.add(parent);
	}

	protected boolean removeChild(final ImplicationVertex<T> child) {
		return mChildren.remove(child);
	}

	protected boolean removeParent(final ImplicationVertex<T> parent) {
		return mParents.remove(parent);
	}

	protected T getPredicate() {
		return mPredicate;
	}

	/**
	 * @return every predicate that is implied by mPredicate (mPredicate is not included)
	 */
	protected Set<ImplicationVertex<T>> getDescendants() {
		final Set<ImplicationVertex<T>> decendants = new HashSet<>(mChildren);
		final Deque<ImplicationVertex<T>> vertex = new ArrayDeque<>(mChildren);
		while (!vertex.isEmpty()) {
			final ImplicationVertex<T> current = vertex.removeFirst();
			decendants.addAll(current.mChildren);
			vertex.addAll(current.mChildren);
		}
		return decendants;
	}
	
	/**
	 * @return every predicate that implies mPredicate (mPredicate is not included)
	 */
	protected Set<ImplicationVertex<T>> getAncestors() {
		final Set<ImplicationVertex<T>> ancestors = new HashSet<>(mParents);
		final Deque<ImplicationVertex<T>> vertex = new ArrayDeque<>(mParents);
		while (!vertex.isEmpty()) {
			final ImplicationVertex<T> current = vertex.removeFirst();
			ancestors.addAll(current.mParents);
			vertex.addAll(current.mParents);
		}
		return ancestors;
	}
}