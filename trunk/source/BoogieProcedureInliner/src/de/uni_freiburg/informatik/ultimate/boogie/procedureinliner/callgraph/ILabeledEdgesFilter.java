package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.model.structure.ILabeledEdgesMultigraph;

/**
 * Filter for labeled edges.
 * This can be used inside graph algorithms to ignore unwanted edges
 * without having to build a modified copy of the graph.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <N> Type of the graph nodes.
 * @param <L> Type of the graph edge labels.
 */
interface ILabeledEdgesFilter<N extends ILabeledEdgesMultigraph<N,L>, L> {
	
	/**
	 * Determines whether to use an outgoing edge or not.
	 * @param source Source node of the edge.
	 * @param outgoingEdgeLabel Label of the edge.
	 * @param target Target node of the edge.
	 * @return The edge should be used.
	 */
	public boolean accept(N source, L outgoingEdgeLabel, N target);
}
