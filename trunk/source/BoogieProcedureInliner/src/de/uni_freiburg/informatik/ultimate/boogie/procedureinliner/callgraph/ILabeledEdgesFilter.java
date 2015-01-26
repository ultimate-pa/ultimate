package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * Filter for labeled edges.
 * This can be used inside graph algorithms to ignore some unwanted edges
 * without having to build a modified copy of the graph.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <L> Type of the edge labels.
 */
interface ILabeledEdgesFilter<L> {
	
	/**
	 * Determines whether to use an outgoing edge or not.
	 * @param outgoingEdgeLabel Label of the outgoing edge to be filtered.
	 * @return The edge should be used.
	 */
	public boolean accept(L outgoingEdgeLabel);
}
