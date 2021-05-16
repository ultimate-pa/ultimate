/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * A simple (not to say, naive) implementation to compute the dominators in a rooted graph. A node v dominates a node w
 * iff all paths from the root to w go through v.
 *
 * TODO If performance warrants it, implement optimized (quasi-linear) algorithm instead.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <V>
 *            The type of nodes in the graph.
 */
public final class DominatorComputation<V> {
	private final Set<V> mNodes;
	private final V mRoot;
	private final Function<V, Set<V>> mGetPredecessors;

	private final Map<V, Set<V>> mDominators = new HashMap<>();

	public DominatorComputation(final Set<V> nodes, final V root, final Function<V, Set<V>> getPredecessors) {
		mNodes = nodes;
		mRoot = root;
		mGetPredecessors = getPredecessors;
		compute();
	}

	private void compute() {
		// initialization
		mDominators.put(mRoot, Collections.singleton(mRoot));
		for (final V node : mNodes) {
			if (!Objects.equals(node, mRoot)) {
				mDominators.put(node, new HashSet<>(mNodes));
			}
		}

		// fix-point iteration
		boolean changes;
		do {
			changes = false;
			for (final V node : mNodes) {
				if (!Objects.equals(node, mRoot)) {
					changes = update(node);
				}
			}
		} while (changes);
	}

	private boolean update(final V node) {
		boolean changes = false;
		final Set<V> predecessors = mGetPredecessors.apply(node);
		final Iterator<V> it = mDominators.get(node).iterator();
		while (it.hasNext()) {
			final V dom = it.next();
			for (final V pred : predecessors) {
				if (!mDominators.get(pred).contains(dom)) {
					it.remove();
					changes = true;
					break;
				}
			}
		}
		return changes;
	}

	public Map<V, Set<V>> getResult() {
		return mDominators;
	}
}