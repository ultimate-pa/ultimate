package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;

public class AuxGraphOperations {

	public static String makeStringInterpretation(GuardGraph automaton) {
		String autRepr = "";
		String autStates = "";
		String autEdges = "";
		final List<GuardGraph> nodes = automaton.getOutgoingNodes();
		autRepr += "Automaton has Nodes: ";
		
		for (GuardGraph node : nodes) {
			for (GuardGraph node2 : nodes) {
				if (!(node.getOutgoingEdgeLabel(node2) == null)) {
					autEdges += "Node: " + node.getLabel() + " transitions to node: " +
							node2.getLabel() + " with edge label: " +
							node.getOutgoingEdgeLabel(node2).toString();
				}
				autEdges += "\n";
			}
			autStates += node.getLabel() + " ";
		}
		autRepr += autStates + "\n" + autEdges;
		
		
		
		return autRepr;
	}
}
