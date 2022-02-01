package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GuardGraph extends ModifiableLabeledEdgesMultigraph<GuardGraph, Term> {

	private static final long serialVersionUID = 94683849463494167L;
	private final int mNodeLabel;
	private final HashMap<Integer, GuardGraph> mNodesMap;
	private final Set<GuardGraph> mBuildingNodes;
	private int mNrOfEdges = 0;

	public GuardGraph(final int label) {
		mNodeLabel = label;
		mNodesMap = new HashMap<>();
		mBuildingNodes = new HashSet<>();
	}

	public GuardGraph(final int label, final Set<GuardGraph> neighbours) {
		mNodeLabel = label;
		mNodesMap = new HashMap<>();
		mBuildingNodes = neighbours;
	}

	public int getNrOfNodes() {
		return getAllNodes().size();
	}

	public void incEdges() {
		mNrOfEdges++;
	}

	public int getNrOfEdges() {
		return mNrOfEdges;
	}

	public Set<GuardGraph> getBuildingNodes() {
		return mBuildingNodes;
	}

	public boolean isSameNode(final GuardGraph node) {
		return mBuildingNodes.containsAll(node.getBuildingNodes())
				&& node.getBuildingNodes().containsAll(mBuildingNodes);
	}

	public int getLabel() {
		return mNodeLabel;
	}

	public Map<Integer, GuardGraph> getAllNodesMap() {
		populateNodes();
		return mNodesMap;
	}

	private void populateNodes() {
		final Set<GuardGraph> allNodes = getAllNodes();
		for (final GuardGraph node : allNodes) {
			mNodesMap.put(node.getLabel(), node);
		}
	}

	@Override
	public String toString() {
		final StringBuilder autRepr = new StringBuilder();
		final StringBuilder autStates = new StringBuilder();
		final StringBuilder autEdges = new StringBuilder();
		autRepr.append("Automaton has Nodes: ");

		for (final GuardGraph node : getAllNodes()) {
			for (final GuardGraph node2 : node.getOutgoingNodes()) {
				if (node.getOutgoingEdgeLabel(node2) != null) {
					autEdges.append(String.format("Node :%s transition to node: %s with edge Label: %s %n",
							node.getLabel(), node2.getLabel(), node.getOutgoingEdgeLabel(node2).toString()));
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
	public Set<GuardGraph> getAllNodes() {
		final Set<GuardGraph> nodes = new HashSet<>();
		final LinkedList<GuardGraph> open = new LinkedList<>();
		open.add(this);
		while (!open.isEmpty()) {
			final GuardGraph peek = open.pop();
			for (final GuardGraph target : peek.getOutgoingNodes()) {
				if (!nodes.contains(target) && !open.contains(target)) {
					open.add(target);
				}
				nodes.add(peek);
			}
		}
		return nodes;
	}
}
