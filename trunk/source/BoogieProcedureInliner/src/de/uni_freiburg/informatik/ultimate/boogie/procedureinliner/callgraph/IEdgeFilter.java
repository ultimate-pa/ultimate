package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * Filter for edges of a graph. This can be used in graph algorithms to ignore unwanted edges without having
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
public interface IEdgeFilter<V, L> {

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
	boolean accept(V source, L outgoingEdgeLabel, V target);
}