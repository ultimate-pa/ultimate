package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class DfgContainer {
	private final HashRelation<DfgNode, DfgNode> edgeRelation;
	private final Set<DfgNode> nodeList;

	public DfgContainer(final HashRelation<DfgNode, DfgNode> edgeRelation, final Set<DfgNode> nodeList) {
		this.edgeRelation = edgeRelation;
		this.nodeList = nodeList;
	}

	public Set<DfgNode> getNodeList() {
		return nodeList;
	}

	public HashRelation<DfgNode, DfgNode> getEdgeRelation() {
		return edgeRelation;
	}
}
