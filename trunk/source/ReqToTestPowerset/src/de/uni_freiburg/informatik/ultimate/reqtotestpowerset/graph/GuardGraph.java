package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GuardGraph extends ModifiableLabeledEdgesMultigraph<GuardGraph, Term> {

	private static final long serialVersionUID = 94683849463494167L;
	private final int mNodeLabel;
	
	public GuardGraph(int label) {
		mNodeLabel = label;
	}

	public int getLabel() {
		return mNodeLabel;
	}
	
	public String toString() {
		StringBuilder autRepr = new StringBuilder();
		StringBuilder autStates = new StringBuilder();
		StringBuilder autEdges = new StringBuilder();
		final List<GuardGraph> nodes = getOutgoingNodes();
		autRepr.append("Automaton has Nodes: ");

		for (GuardGraph node : nodes) {
			for (GuardGraph node2 : nodes) {
				if (!(node.getOutgoingEdgeLabel(node2) == null)) {
					autEdges.append(String.format("Node :%s transition to node: %s with edge Label: %s \n", 
							node.getLabel(),node2.getLabel(),node.getOutgoingEdgeLabel(node2).toString()));
				}
			}
			autStates.append(node.getLabel());
			autStates.append( " ");
		}
		autRepr.append(autStates);
		autRepr.append("\n");
		autRepr.append(autEdges);

		return autRepr.toString();
	}
}
