package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GuardGraph extends ModifiableLabeledEdgesMultigraph<GuardGraph, Term> {

	private static final long serialVersionUID = 94683849463494167L;
	private final int mNodeLabel;
	private HashMap<Integer, GuardGraph> mNodesMap;
	private final Set<GuardGraph> mBuildingNodes;
	private int nrOfEdges = 0;
	
	public GuardGraph(int label) {
		mNodeLabel = label;
		mNodesMap = new HashMap<Integer, GuardGraph>();
		mBuildingNodes = new HashSet<GuardGraph>();
	}

	public GuardGraph(int label, Set<GuardGraph> neighbours) {
		mNodeLabel = label;
		mNodesMap = new HashMap<Integer, GuardGraph>();
		mBuildingNodes = neighbours;
	}
	
	public int getNrOfNodes() {
		return getAllNodes().size();
	}
	
	public void incEdges() {
		nrOfEdges++;
	}
	
	public int getNrOfEdges() {
		return nrOfEdges;
	}
	
	public Set<GuardGraph> getBuildingNodes() {
		return mBuildingNodes;
	}
	
	public boolean isSameNode(GuardGraph node) {
		if (mBuildingNodes.containsAll(node.getBuildingNodes()) && node.getBuildingNodes().containsAll(mBuildingNodes)) {
			return true;
		} else {
			return false;
		}
	}
	
	public int getLabel() {
		return mNodeLabel;
	}
	
	public HashMap<Integer, GuardGraph> getAllNodesMap() {
		populateNodes();
		return mNodesMap;
	}
	
	private void populateNodes() {
		Set<GuardGraph> allNodes = getAllNodes();
		for (GuardGraph node : allNodes) {
			mNodesMap.put(node.getLabel(), node);
		}
	}

	
	public String toString() {
		StringBuilder autRepr = new StringBuilder();
		StringBuilder autStates = new StringBuilder();
		StringBuilder autEdges = new StringBuilder();
		autRepr.append("Automaton has Nodes: ");

		for (GuardGraph node : getAllNodes()) {
			for (GuardGraph node2 : node.getOutgoingNodes()) {
				if (!(node.getOutgoingEdgeLabel(node2) == null)) {
					autEdges.append(String.format("Node :%s transition to node: %s with edge Label: %s \n", 
							node.getLabel(),node2.getLabel(),node.getOutgoingEdgeLabel(node2).toString()));
				}
			}
			autStates.append(node.getLabel());
			autStates.append(" ");
		}
		autRepr.append(autStates);
		autRepr.append("\n");
		autRepr.append(autEdges);

		return autRepr.toString();
	}

	// expand to return value HashMap<int, GuardGraph> int is label
	public Set<GuardGraph> getAllNodes(){
		Set<GuardGraph> nodes = new HashSet<>();
		LinkedList<GuardGraph> open = new LinkedList<GuardGraph>();
		open.add(this);
		while(open.size() > 0) {
			GuardGraph peek =  open.pop();
			for(GuardGraph target: peek.getOutgoingNodes()) {
				if(!nodes.contains(target) && !open.contains(target)) {
					open.add(target);
				}
				nodes.add(peek);
			}
		}
		return nodes;
	}
}
