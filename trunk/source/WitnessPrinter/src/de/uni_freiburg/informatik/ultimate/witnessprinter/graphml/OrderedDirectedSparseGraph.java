package de.uni_freiburg.informatik.ultimate.witnessprinter.graphml;

import java.util.LinkedHashMap;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

/**
 * Change the default {@link DirectedSparseGraph} s.t. the nodes and edges written are ordered lexicographically.
 * DirectedSparseGraph
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
final class OrderedDirectedSparseGraph<VERTEX, EDGE, TE, E> extends DirectedSparseGraph<VERTEX, EDGE> {
	private static final long serialVersionUID = -8539872407688620571L;

	public OrderedDirectedSparseGraph() {
		vertices = new LinkedHashMap<>();
		edges = new LinkedHashMap<>();
	}
}
