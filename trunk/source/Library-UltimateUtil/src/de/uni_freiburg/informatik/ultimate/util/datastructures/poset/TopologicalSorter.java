/*
 * Copyright (C) 2015-2019 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * Utility class for topological sorting of DAGs.
 *
 * @param <V> Type of the graph's nodes.
 *
 * @author schaetzc@tf.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class TopologicalSorter<V> {

	private Set<V> mUnmarkedNodes;
	private Set<V> mTemporarilyMarkedNodes;
	private List<V> mTopolicalSorting;

	private final Function<V, Collection<V>> mSuccesorsOf;

	/**
	 * Creates re-usable sorter.
	 * Instead of the actual successor function one can pass an altered version that ignores some edges.
	 * This can be used to sort graphs with cycles if the cycle building edges are ignored.
	 * @param funSuccesor A deterministic function that provides all successors for a vertex.
	 */
	public TopologicalSorter(final Function<V, Collection<V>> funSuccesor) {
		mSuccesorsOf = funSuccesor;
	}

	/** @see #reversedTopologicalOrdering(Collection) */
	public Optional<List<V>> topologicalOrdering(final Collection<V> graphNodes) {
		final Optional<List<V>> ordering = reversedTopologicalOrdering(graphNodes);
		ordering.ifPresent(Collections::reverse);
		return ordering;
	}

	/**
	 * Creates a reversed topological ordering of an acyclic directed graph (DAG) given as a set of nodes.
	 * The given set of nodes must be closed under the successor function specified in {@link #TopologicalSorter(Function)}.
	 * @param graphNodes Closed set of nodes to be sorted. Duplicates will be ignored.
	 * @return Reversed topological ordering of the nodes iff such an ordering exists
	 */
	public Optional<List<V>> reversedTopologicalOrdering(final Collection<V> graphNodes) {
		try {
			return Optional.of(tryRevTopSort(graphNodes));
		} catch (final GraphCycleException gce) {
			return Optional.empty();
		}
	}

	/**
	 * Tries to sort a set of nodes topologically.
	 * @param graphNodes Nodes to be sorted, must be closed under {@link #mSuccesorsOf}. Duplicates will be ignored.
	 * @return Reversed topological ordering of the nodes
	 * @throws GraphCycleException The set of nodes contained a cycle under {@link #mSuccesorsOf}
	 */
	private List<V> tryRevTopSort(final Collection<V> graphNodes) throws GraphCycleException {
		mUnmarkedNodes = new LinkedHashSet<>(graphNodes);
		mTemporarilyMarkedNodes = new HashSet<>();
		mTopolicalSorting = new ArrayList<>(graphNodes.size());
		while (!mUnmarkedNodes.isEmpty()) {
			visit(mUnmarkedNodes.iterator().next());
		}
		return mTopolicalSorting;
	}

	// DFS-based algorithm from "http://en.wikipedia.org/wiki/Topological_sorting" (Tarjan, 1976)
	private void visit(final V node) throws GraphCycleException {
		if (mTemporarilyMarkedNodes.contains(node)) {
			throw new GraphCycleException();
		} else if (mUnmarkedNodes.contains(node)) {
			markTemporarily(node);
			for (final V successorNode : mSuccesorsOf.apply(node)) {
				visit(successorNode);
			}
			markPermanently(node);
			mTopolicalSorting.add(node);
		}
	}

	private void markTemporarily(final V unmarkedNode) {
		mTemporarilyMarkedNodes.add(unmarkedNode);
	}

	private void markPermanently(final V temporarilyMarkedNode) {
		mTemporarilyMarkedNodes.remove(temporarilyMarkedNode);
		mUnmarkedNodes.remove(temporarilyMarkedNode);
	}

	private static class GraphCycleException extends Exception {
		private static final long serialVersionUID = -7189895863479876025L;
	}
}
