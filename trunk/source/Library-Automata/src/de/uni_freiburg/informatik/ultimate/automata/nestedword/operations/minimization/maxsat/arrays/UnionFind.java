/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

final class UnionFind {
	private int[] mRoot;
	private final int[] mSize;
	private final int[] mStack;

	UnionFind(final int numNodes) {
		mRoot = new int[numNodes];
		mSize = new int[numNodes];
		mStack = new int[numNodes];

		for (int i = 0; i < numNodes; i++) {
			mRoot[i] = i;
			mSize[i] = 1;
		}
	}

	/**
	 * Add an edge between two nodes. This makes them equivalent and they will be together, with a root right over their
	 * heads. They'll share the same root, yeah!
	 *
	 * @param n1
	 *            The one node.
	 * @param n2
	 *            The other node, you know?
	 */
	void merge(int n1, int n2) {
		updateRoot(n1);
		updateRoot(n2);

		n1 = mRoot[n1];
		n2 = mRoot[n2];

		if (n1 == n2) {
			return;
		}

		if (mSize[n1] < mSize[n2]) {
			mRoot[n1] = n2;
			mSize[n2] += mSize[n1];
		} else {
			mRoot[n2] = n1;
			mSize[n1] += mSize[n2];
		}
	}

	int[] extractRoots() {
		for (int i = 0; i < mRoot.length; i++) {
			updateRoot(i);
		}

		final int[] result = mRoot;

		mRoot = null;
		return result;
	}

	private void updateRoot(int node) {
		int ptr = 0;

		while (node != mRoot[node]) {
			mStack[ptr++] = node;
			node = mRoot[node];
		}
		while (ptr-- > 0) {
			mRoot[mStack[ptr]] = node;
		}
	}
}
