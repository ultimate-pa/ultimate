/*
 * Copyright (C) 2015-2018 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
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
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

/**
 * Utility class for topological sorting of DAGs.
 *
 * @param <V>
 *            Type of the graph's nodes.
 * @param <L>
 *            Type of the graph's edge labels.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class TopologicalSorter<V, L> {

	private Set<V> mUnmarkedNodes;
	private Set<V> mTemporarilyMarkedNodes;
	private Set<V> mPermanentlyMarkedNodes;
	private List<V> mTopolicalSorting;

	private final Function<V, Collection<Entry<V, L>>> mFunSuccesor;
	private final IRelationFilter<V, L> mOutgoingEdgesFilter;

	/**
	 * Create a sorter for a given DAG.
	 *
	 * @param funSuccesor
	 *            A function that provides all successors and their respective edge labels for a vertex.
	 */
	public TopologicalSorter(final Function<V, Collection<Entry<V, L>>> funSuccesor) {
		this(funSuccesor, (source, outgoingEdgeLabel, target) -> true);
	}

	/**
	 * Create a sorter that ignores some of the graphs edges. This can be used to sort an graph with cycles, if the
	 * cycle building edges are rejected by the filter.
	 *
	 * @param funSuccesor
	 *            A function that provides all successors and their respective edge labels for a vertex.
	 * @param outgoingEdgesFilter
	 *            Filter to be applied on successor edges -- only accepted edges will be used.
	 */
	public TopologicalSorter(final Function<V, Collection<Entry<V, L>>> funSuccesor,
			final IRelationFilter<V, L> outgoingEdgesFilter) {
		mOutgoingEdgesFilter = outgoingEdgesFilter;
		mFunSuccesor = funSuccesor;
	}

	/** @see #reversedTopologicalOrdering(Collection) */
	public List<V> topologicalOrdering(final Collection<V> graph) {
		final List<V> ordering = reversedTopologicalOrdering(graph);
		if (ordering != null) {
			Collections.reverse(ordering);
		}
		return ordering;
	}

	/**
	 * Creates a reversed topological ordering of an acyclic directed graph (DAG). There are no guarantees, if a node
	 * inside <code>graph</code> has a child that isn't part of <code>graph</code> (except if the edge from the node to
	 * it's child isn't accept by the filter).
	 *
	 * @param graph
	 *            All nodes of the graph to be sorted. Duplicates will be ignored.
	 * @return Topological ordering of the nodes. null iff the graph contained a circle.
	 */
	public List<V> reversedTopologicalOrdering(final Collection<V> graph) {
		mUnmarkedNodes = new HashSet<>(graph);
		mTemporarilyMarkedNodes = new HashSet<>();
		mPermanentlyMarkedNodes = new HashSet<>();
		mTopolicalSorting = new ArrayList<>(graph.size());
		while (!mUnmarkedNodes.isEmpty()) {
			try {
				visit(mUnmarkedNodes.iterator().next());
			} catch (final GraphCycleException gce) {
				return null;
			}
		}
		return mTopolicalSorting;
	}

	// DFS-based algorithm from "http://en.wikipedia.org/wiki/Topological_sorting" (Tarjan, 1976)
	private void visit(final V node) throws GraphCycleException {
		if (mTemporarilyMarkedNodes.contains(node)) {
			throw new GraphCycleException();
		} else if (mUnmarkedNodes.contains(node)) {
			markTemporarily(node);

			for (final Entry<V, L> outgoingNode : mFunSuccesor.apply(node)) {
				if (mOutgoingEdgesFilter.accept(node, outgoingNode.getValue(), outgoingNode.getKey())) {
					visit(outgoingNode.getKey());
				}
			}
			markPermanently(node);
			mTopolicalSorting.add(node);
		}
	}

	private void markTemporarily(final V unmarkedNode) {
		mUnmarkedNodes.remove(unmarkedNode);
		mTemporarilyMarkedNodes.add(unmarkedNode);
	}

	private void markPermanently(final V temporarilyMarkedNode) {
		mTemporarilyMarkedNodes.remove(temporarilyMarkedNode);
		mPermanentlyMarkedNodes.add(temporarilyMarkedNode);
	}

	private static class GraphCycleException extends Exception {
		private static final long serialVersionUID = -7189895863479876025L;
	}

	/**
	 * Filter for, e.g., labeled edges. This can be used inside graph algorithms to ignore unwanted edges without having
	 * to build a modified copy of the graph.
	 *
	 * @author schaetzc@informatik.uni-freiburg.de
	 *
	 * @param <V>
	 *            Type of the graph nodes.
	 * @param <L>
	 *            Type of the graph edge labels.
	 */
	@FunctionalInterface
	public interface IRelationFilter<V, L> {

		/**
		 * Determines whether to use an outgoing edge or not.
		 *
		 * @param source
		 *            Source node of the edge.
		 * @param outgoingEdgeLabel
		 *            Label of the edge.
		 * @param target
		 *            Target node of the edge.
		 * @return The edge should be used.
		 */
		public boolean accept(V source, L outgoingEdgeLabel, V target);
	}
}
