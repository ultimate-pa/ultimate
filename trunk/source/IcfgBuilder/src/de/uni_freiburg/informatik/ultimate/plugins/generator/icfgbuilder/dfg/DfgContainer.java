package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class DfgContainer {
	private final HashRelation<DFGNode, DFGNode> edgeRelation;
	private final Set<DFGNode> nodeList;

	public DfgContainer(final HashRelation<DFGNode, DFGNode> edgeRelation, final Set<DFGNode> nodeList) {
		this.edgeRelation = edgeRelation;
		this.nodeList = nodeList;
	}

	public Set<DFGNode> getNodeList() {
		return nodeList;
	}

	public HashRelation<DFGNode, DFGNode> getEdgeRelation() {
		return edgeRelation;
	}
}
