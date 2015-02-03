package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * Call graph edge filter, accepting only non-recursive, normal calls.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class SimpleCallFilter implements ILabeledEdgesFilter<CallGraphNode, CallGraphEdgeLabel> {

	@Override
	public boolean accept(CallGraphNode source, CallGraphEdgeLabel outgoingEdgeLabel, CallGraphNode target) {
		return outgoingEdgeLabel.getEdgeType().isSimpleCall();
	}

}
