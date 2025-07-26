/*
 * Copyright (C) 2025 Christof Schuster (christof.schuster@gmx.de)
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

import java.util.Map.Entry;
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
	private static final boolean MULTI_LINE_TO_STRING = true;
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
		if (!MULTI_LINE_TO_STRING) {
			return "DfgContainer [mEdgeRelation=" + mEdgeRelation + ", mNodeList=" + mNodeList + "]";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Nodes:");
		sb.append(System.lineSeparator());
		for (final DfgNode node : mNodeList) {
			sb.append(node);
			sb.append(System.lineSeparator());
		}
		sb.append("Edges:");
		sb.append(System.lineSeparator());
		for (final Entry<DfgNode, DfgNode> entry : mEdgeRelation) {
			sb.append(entry.getKey());
			sb.append("    --->    ");
			sb.append(entry.getValue());
			sb.append(System.lineSeparator());
		}
		return sb.toString();
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
