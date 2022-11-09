/*
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class ComputeSCC<V> {

	ComputeSuccessor<V> mComputeSuccs;

	public ComputeSCC(ComputeSuccessor<V> computeSuccs) {
		mComputeSuccs = computeSuccs;
	}

	/**
	 * Return the SCCs of the graph in reverse topological order. SCCs with no
	 * outgoing edges are first in the list. An SCC with outgoing edges comes after
	 * all its successor SCCs.
	 *
	 * @param entryPoints an iterator over all nodes of the graph.
	 * @return the list of SCCs, each SCC being a list of vertices.
	 */
	public List<List<V>> getSCCs(Iterator<V> entryPoints) {
		// Tarjan's algorithm implemented in non-recursive style.
		final List<List<V>> allSCCs = new ArrayList<>();
		final ArrayList<V> currentPath = new ArrayList<>();
		final ArrayList<StackEntry<V>> stack = new ArrayList<>();
		final HashSet<V> visited = new HashSet<>();
		final Map<V, Integer> positionInPath = new HashMap<>();
		int cycleHead = -1;
		Iterator<V> currentIterator = entryPoints;
		V parent = null;
		while (true) {
			if (currentIterator.hasNext()) {
				// process next child
				final V child = currentIterator.next();
				if (visited.add(child)) {
					// visit a new child
					visited.add(child);
					positionInPath.put(child, currentPath.size());
					stack.add(new StackEntry<>(cycleHead, currentIterator, parent));
					currentIterator = mComputeSuccs.getSuccessors(child);
					cycleHead = currentPath.size();
					currentPath.add(child);
					parent = child;
				} else {
					// already visited, check for cycle.
					final Integer prevOnPath = positionInPath.get(child);
					if (prevOnPath != null) {
						// we found a cycle. Extend the current cycle
						if (cycleHead > prevOnPath) {
							cycleHead = prevOnPath;
						}
					}
				}
			} else {
				if (stack.isEmpty()) {
					// we are done
					return allSCCs;
				}
				if (parent == currentPath.get(cycleHead)) {
					// this is the first node in an SCC. Build the SCC and add it to result list.
					final List<V> cycle = currentPath.subList(cycleHead, currentPath.size());
					allSCCs.add(new ArrayList<>(cycle));
					for (final V v : cycle) {
						positionInPath.remove(v);
					}
					cycle.clear();
				}
				final StackEntry<V> caller = stack.remove(stack.size() - 1);
				parent = caller.mVertex;
				currentIterator = caller.mIterator;
				if (caller.mPrevCycleHead < cycleHead) {
					cycleHead = caller.mPrevCycleHead;
				}
			}
		}
	}

	private static class StackEntry<V> {
		int mPrevCycleHead;
		Iterator<V> mIterator;
		V mVertex;

		public StackEntry(int cycleHead, Iterator<V> iterator, V vertex) {
			mPrevCycleHead = cycleHead;
			mIterator = iterator;
			mVertex = vertex;
		}
	}

	public static interface ComputeSuccessor<V> {
		public Iterator<V> getSuccessors(V node);
	}
}
