/*
 * Code taken from https://github.com/johspaeth/PathExpression
 * Copyright (C) 2018 Johannes Spaeth
 * Copyright (C) 2018 Fraunhofer IEM, Paderborn, Germany
 * 
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-PathExpressions plug-in.
 *
 * The ULTIMATE Library-PathExpressions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-PathExpressions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-PathExpressions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-PathExpressions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-PathExpressions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pathexpressions;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledEdge;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledGraph;

public class GenericLabeledGraph<N, L> implements ILabeledGraph<N, L> {

	protected final Set<N> mNodes;
	protected final Set<ILabeledEdge<N, L>> mEdges;

	public GenericLabeledGraph() {
		this(new HashSet<>(), new HashSet<>());
	}

	protected GenericLabeledGraph(Set<N> nodes, Set<ILabeledEdge<N, L>> edges) {
		mNodes = nodes;
		mEdges = edges;
	}

	/**
	 * Adds a node to this graph. Already existing nodes are ignored.
	 * <p>
	 * Nodes can also be added implicitly using {@link #addEdge(ILabeledEdge)}
	 * so calling this method might not be necessary.
	 * 
	 * @param node Node to be added
	 * @return The node was new (did not already exist), the node was added
	 */
	public boolean addNode(final N node) {
		return mNodes.add(node);
	}

	/**
	 * Adds an edge to this graph. Already existing edges are ignored.
	 * <p>
	 * Source and target nodes of the edge are also added to this graph.
	 * Calling {@link #addNode(Object)} is not necessary.
	 * 
	 * @param edge Edge to be added
	 * @return The edge was new (did not already exist), the edge was added
	 */
	public boolean addEdge(final ILabeledEdge<N, L> edge) {
		addNode(edge.getSource());
		addNode(edge.getTarget());
		return mEdges.add(edge);
	}

	/**
	 * Constructs and adds an edge to this graph. Already existing edges are ignored.
	 * <p>
	 * Source and target nodes of the edge are also added to this graph.
	 * Calling {@link #addNode(Object)} is not necessary.
	 * 
	 * @param source Source node of the new edge
	 * @param label Label of the new edge
	 * @param target Target node of the edge
	 * @return The edge was new (did not already exist), the edge was added
	 */
	public boolean addEdge(final N source, final L label, final N target) {
		return addEdge(new GenericLabeledEdge<N, L>(source, label, target));
	}

	@Override
	public Set<ILabeledEdge<N, L>> getEdges() {
		return mEdges;
	}

	@Override
	public Set<N> getNodes() {
		return mNodes;
	}
	
	@Override
	public String toString() {
		return "nodes = " + mNodes + " edges = " + mEdges;
	}
}
