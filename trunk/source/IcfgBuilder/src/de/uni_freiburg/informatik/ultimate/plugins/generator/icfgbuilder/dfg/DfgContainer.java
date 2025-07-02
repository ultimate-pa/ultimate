package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * This class represents the Data Flow Graph of a Boogie Control Flow Graph. It is represented via a Nodelist and a
 * Relation between Nodes that represent the edges of the graph.
 *
 * @author christof.schuster@gmx.de
 */
public class DfgContainer {
	private final HashRelation<DfgNode, DfgNode> mEdgeRelation;
	private final Set<DfgNode> mNodeList;

	public DfgContainer(final HashRelation<DfgNode, DfgNode> edgeRelation, final Set<DfgNode> nodeList) {
		mEdgeRelation = edgeRelation;
		mNodeList = nodeList;
	}

	/**
	 *
	 * @return the Nodelist of this Graph
	 */
	public Set<DfgNode> getNodeList() {
		return mNodeList;
	}

	/**
	 *
	 * @return the relation between Nodes of the Graph that represent Edges
	 */
	public HashRelation<DfgNode, DfgNode> getEdgeRelation() {
		return mEdgeRelation;
	}

	@Override
	public String toString() {
		return "DfgContainer [mEdgeRelation=" + mEdgeRelation + ", mNodeList=" + mNodeList + "]";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mEdgeRelation, mNodeList);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DfgContainer other = (DfgContainer) obj;
		return Objects.equals(mEdgeRelation, other.mEdgeRelation) && Objects.equals(mNodeList, other.mNodeList);
	}
}
