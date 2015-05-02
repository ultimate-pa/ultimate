package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Labels the nodes of a Boogie call graph.
 * <p>
 * Note, that call-foralls aren't treated other than normal calls.
 * This is not a real problem, but might be inefficient in some (constructed) cases.
 * 
 * @see CallGraphNodeLabel
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class NodeLabeler {

	private Collection<String> mEntryProcedures;
	
	private Map<String, CallGraphNode> mCallGraph;
	private Set<CallGraphEdgeLabel> mVisitedEdges;
	private Set<String> mEntryAndReEntryProcedures;

	public NodeLabeler(Collection<String> entryPorcedures) {
		mEntryProcedures = entryPorcedures;
	}
	
	/**
	 * Sets the node labels for a call graph.
	 * <p>
	 * The inline flags for the call graph edges should have their final value assigned,
	 * because the node labels depend on the inline flags.
	 * 
	 * @param callGraph Boogie call graph, which's inline flags don't change anymore.
	 * 
	 * @return Identifiers from all existing procedures, marked as entry or re-entry procedures.
	 * 
	 * @see CallGraphNodeLabel
	 */
	public Set<String> label(Map<String, CallGraphNode> callGraph) {
		reset();
		mCallGraph = callGraph;
		for (String entryId : mEntryProcedures) {
			CallGraphNode entryNode = callGraph.get(entryId);
			if (entryNode != null) {
				entryNode.setLabel(CallGraphNodeLabel.ENTRY);
				mEntryAndReEntryProcedures.add(entryId);
				visitChilds(entryNode);
			}
		}
		labelNonLabeledNodesAsDead();
		return mEntryAndReEntryProcedures;
	}

	private void reset() {
		mCallGraph = null;
		mVisitedEdges = new HashSet<>();
		mEntryAndReEntryProcedures = new HashSet<>();
	}

	private void visitChilds(CallGraphNode source) {
		Iterator<CallGraphEdgeLabel> arcs = source.getOutgoingEdgeLabels().iterator();
		Iterator<CallGraphNode> targets = source.getOutgoingNodes().iterator();
		while (arcs.hasNext() && targets.hasNext()) {
			CallGraphNode target = targets.next();
			CallGraphEdgeLabel arc = arcs.next();
			boolean arcAlreadyVisited = !mVisitedEdges.add(arc);
			if (arcAlreadyVisited || target.getLabel() != null)
				continue;
			if (!arc.getInlineFlag()) {
				target.setLabel(CallGraphNodeLabel.RE_ENTRY);
				mEntryAndReEntryProcedures.add(target.getId());
			}
			visitChilds(target);
		}
	}
	
	private void labelNonLabeledNodesAsDead() {
		for (CallGraphNode node : mCallGraph.values()) {
			if (node.getLabel() == null) {
				node.setLabel(CallGraphNodeLabel.DEAD);
			}
		}
	}

}
