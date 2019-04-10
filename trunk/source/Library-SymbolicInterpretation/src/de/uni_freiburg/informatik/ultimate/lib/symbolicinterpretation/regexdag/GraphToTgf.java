/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE SymbolicInterpretation plug-in.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.function.Function;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.models.IDirectedGraph;

// TODO move this class to a util/model project

/**
 * Converts an {@link IDirectedGraph} into Trivial Graph Format (TGF).
 * Nodes can be labeled by a custom function.
 * There are no explicit edges in {@linkplain IDirectedGraph}, therefore the edges are not labeled with data.
 * <p>
 * Some implementations of {@linkplain IDirectedGraph} can represent edges non-symmetrically, that is
 * a node U can have successor V not having U as a predecessor. To show such issues the generated TGF
 * represents directed edges by <i>forward</i> edges and (hopefully anti-parallel) <i>backward</i> edges.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <N> Type of the graph nodes
 */
public class GraphToTgf<N extends IDirectedGraph<N, ?>> {

	private final StringBuilder mTgfNodes = new StringBuilder();
	private final StringBuilder mTgfEdges = new StringBuilder();
	private final Map<N, Integer> mVisitedNodeToId = new HashMap<>();
	private final Queue<N> mWorklist = new ArrayDeque<>();
	private final Function<N, Object> mNodeToLabel;

	public GraphToTgf(final N startingNode) {
		this(startingNode, N::toString);
	}

	public GraphToTgf(final N startingNode, final Function<N, Object> nodeToLabel) {
		mNodeToLabel = nodeToLabel;
		visit(startingNode);
		traverse();
	}

	public String getTgf() {
		return mTgfNodes + "#\n" + mTgfEdges; 
	}

	private void traverse() {
		while (!mWorklist.isEmpty()) {
			final N current = mWorklist.remove();
			visitNeighbors(current);
			addEdges(current);
		}
	}

	private void visitNeighbors(final N node) {
		Stream.concat(node.getIncomingNodes().stream(), node.getOutgoingNodes().stream())
			.filter(this::isUnvisited)
			.forEach(this::visit);
	}

	private int visit(final N node) {
		final int id = mVisitedNodeToId.size();
		mVisitedNodeToId.put(node, id);
		mTgfNodes.append(id).append(' ').append(mNodeToLabel.apply(node)).append("\n");
		mWorklist.add(node);
		return id;
	}

	private void addEdges(final N source) {
		final int sourceId = idOf(source);
		source.getIncomingNodes().forEach(target -> addEdge(sourceId, idOf(target), " backward"));
		source.getOutgoingNodes().forEach(target -> addEdge(sourceId, idOf(target), " forward"));
	}

	private void addEdge(final int source, final int target, final String label) {
		mTgfEdges.append(source).append(' ').append(target).append(" ").append(label).append("\n");
	}

	private int idOf(final N node) {
		return mVisitedNodeToId.get(node);
	}

	private boolean isUnvisited(final N node) {
		return !mVisitedNodeToId.containsKey(node);
	}
}
