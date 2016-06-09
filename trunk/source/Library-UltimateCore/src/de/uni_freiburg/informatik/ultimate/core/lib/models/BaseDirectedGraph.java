/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IDirectedGraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/**
 * Reference implementation of the {@link IDirectedGraph} interface.
 * 
 * @author dietsch
 * @see IDirectedGraph
 * @see BasePayloadContainer
 * 
 */
public abstract class BaseDirectedGraph<T extends IDirectedGraph<T, VisualizationNode>> extends BasePayloadContainer
		implements IDirectedGraph<T, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<T> mOutgoingNodes;

	protected List<T> mIncomingNodes;

	/***
	 * This constructor creates a directed graph node without a predecessor and without a payload.
	 */
	protected BaseDirectedGraph() {
		this(null, null);
	}

	/**
	 * This constructor creates a directed graph node without a predecessor but with a given payload.
	 * 
	 * @param payload
	 *            A given payload or null
	 */
	protected BaseDirectedGraph(IPayload payload) {
		this(null, payload);

	}

	/**
	 * This constructor creates a directed graph node with a given predecessor node but without a payload.
	 * 
	 * @param parent
	 *            A given parent node or null. If the given parent node is not null, this node will be added to the
	 *            parent's list of outgoing nodes and the parent will be added to this node's list of incoming nodes.
	 */
	protected BaseDirectedGraph(T parent) {
		this(parent, null);
	}

	/**
	 * This constructor creates a directed graph node with a given predecessor node and a given payload.
	 * 
	 * @param parent
	 *            A given parent node or null. If the given parent node is not null, this node will be added to the
	 *            parent's list of outgoing nodes and the parent will be added to this node's list of incoming nodes.
	 * @param payload
	 *            A given payload or null
	 */
	@SuppressWarnings("unchecked")
	protected BaseDirectedGraph(T parent, IPayload payload) {
		super(payload);
		mOutgoingNodes = new ArrayList<T>();
		mIncomingNodes = new ArrayList<T>();
		if (parent != null) {
			mIncomingNodes.add(parent);
			parent.getOutgoingNodes().add((T) this);
		}
	}

	@Override
	public List<T> getIncomingNodes() {
		return mIncomingNodes;
	}

	@Override
	public List<T> getOutgoingNodes() {
		return mOutgoingNodes;
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<IWalkable> getSuccessors() {
		return (List<IWalkable>) getOutgoingNodes();
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

}
