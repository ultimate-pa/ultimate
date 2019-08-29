/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.GraphToTgf;

/**
 * Converts a list of edges into a string using the Trivial Graph Format (TGF) file format.
 * TGF files can be interpreted as directed or undirected graphs –
 * this information itself isn't stored in TGF files.
 * <p>
 * The graph has to be enumerated manually using {@link #addEdge(N, Object, N)}
 * (and {@link #addDisconnectedNode(N)} if there are any disconnected nodes).
 * The resulting TGF is returned by {@link #toString()}.
 * <p>
 * Nodes in the graph are identified by object equality according to {@link Object#equals(Object)}
 * and labeled using the canonical string representation {@link Object#toString()}. The same edge
 * can be added multiple times. {@code null} nodes and edge labels are supported.
 * <p>
 *
 * @param <N> Type of the nodes in the graph. It is perfectly fine to use {@code Object} here.
 *            However, you might want to use a more concrete type to prevent accidentally using the wrong
 *            objects as nodes.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @see GraphToTgf Converts a given graph to TGF without having to manually add edges and nodes
 */
public class TgfBuilder<N> {

	private final StringBuilder mTgfNodes = new StringBuilder();
	private final StringBuilder mTgfEdges = new StringBuilder();
	private final Map<N, Integer> mNodeToId = new HashMap<>();

	public TgfBuilder<N> addEdge(final N sourceNode, final Object edgeLabel, final N targetNode) {
		mTgfEdges
			.append(nodeId(sourceNode)).append(' ')
			.append(nodeId(targetNode)).append(' ')
			.append(labelOf(edgeLabel)).append('\n');
		return this;
	}

	public TgfBuilder<N> addDisconnectedNode(final N node) {
		nodeId(node);
		return this;
	}

	private int nodeId(final N node) {
		return mNodeToId.computeIfAbsent(node, this::computeNewNodeIdAndAddToTgf);
	}

	private int computeNewNodeIdAndAddToTgf(final N node) {
		final int id = mNodeToId.size();
		mTgfNodes.append(id).append(' ').append(labelOf(node)).append('\n');
		return id;
	}

	private static String labelOf(final Object nodeOrEdge) {
		// A newline in a label would break the TGF format
		return nodeOrEdge.toString().replace('\n', '¶');
	}

	@Override
	public String toString() {
		return new StringBuilder()
			.append(mTgfNodes)
			.append("#\n")
			.append(mTgfEdges)
			.toString();
	}

	public void reset() {
		mTgfNodes.setLength(0);
		mTgfEdges.setLength(0);
		mNodeToId.clear();
	}
}
