package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;

/**
 * Interface for setting the {@link CallGraphEdgeLabel#getInlineFlag()} values of all call graph edges.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public interface IInlineSelector {

	/**
	 * Set the {@link CallGraphEdgeLabel#getInlineFlag()} value of all call graph edges.
	 * @param callGraph Mapping from all procedure identifiers to the nodes of the call graph.
	 */
	public void setInlineFlags(Map<String, CallGraphNode> callGraph);

}
