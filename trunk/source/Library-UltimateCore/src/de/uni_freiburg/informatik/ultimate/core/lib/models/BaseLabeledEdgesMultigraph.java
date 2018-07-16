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

import de.uni_freiburg.informatik.ultimate.core.model.models.ILabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/***
 * Basic implementation of the {@link ILabeledEdgesMultigraph} interface.
 *
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare
 *            <tt>public final class FinalModel implements ILabeledEdgesMultigraph&lt;FinalModel,L&gt;</tt> .
 * @param <L>
 *            The type of the edge labels.
 *
 * @author dietsch
 * @see ILabeledEdgesMultigraph
 */
public abstract class BaseLabeledEdgesMultigraph<T extends BaseLabeledEdgesMultigraph<T, L>, L>
		extends BasePayloadContainer implements ILabeledEdgesMultigraph<T, L, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<T> mOutgoingNodes;

	protected List<T> mIncomingNodes;

	protected List<L> mOutgoingEdgeLabels;

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without connections to any other node and without
	 * a payload.
	 */
	protected BaseLabeledEdgesMultigraph() {
		this(null, null, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without connections to any other node but with a
	 * given payload.
	 *
	 * @param payload
	 *            The payload for the current node or null.
	 * @see IPayload
	 */
	protected BaseLabeledEdgesMultigraph(final IPayload payload) {
		this(null, null, payload);

	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without a payload. It modifies a given
	 * BaseLabeledEdgesMultigraph node such that it becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node). The new edge from the given node to the new
	 * node is not labeled.
	 *
	 * @param parent
	 *            A node that should become the predecessor of this node or null.
	 */
	protected BaseLabeledEdgesMultigraph(final T parent) {
		this(parent, null, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without a payload. It modifies a given
	 * BaseLabeledEdgesMultigraph node such that it becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node). The new edge from the given node to the new
	 * node is labeled with a given edge label.
	 *
	 * @param parent
	 *            A node that should become the predecessor of this node or null.
	 * @param incomingEdgeLabel
	 *            A label for the edge from the predecessor to the new node or null. If the predecessor is null, this
	 *            label will be ignored.
	 */
	protected BaseLabeledEdgesMultigraph(final T parent, final L incomingEdgeLabel) {
		this(parent, incomingEdgeLabel, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node with a given payload, modifies a given
	 * BaseLabeledEdgesMultigraph node such that it becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node), and labels the edge from the predecessor to
	 * the new node with a given edge label.
	 *
	 * @param predecessor
	 *            A node that should become the predecessor of this node or null.
	 * @param incomingEdgeLabel
	 *            A label for the edge from the predecessor to the new node or null. If the predecessor is null, this
	 *            label will be ignored.
	 * @param payload
	 *            A payload for the new node or null.
	 * @see IPayload
	 */
	@SuppressWarnings("unchecked")
	protected BaseLabeledEdgesMultigraph(final T predecessor, final L incomingEdgeLabel, final IPayload payload) {
		super(payload);
		mOutgoingEdgeLabels = new ArrayList<>();
		mOutgoingNodes = new ArrayList<>();
		mIncomingNodes = new ArrayList<>();
		if (predecessor != null) {
			predecessor.mOutgoingEdgeLabels.add(incomingEdgeLabel);
			predecessor.mOutgoingNodes.add((T) this);
			mIncomingNodes.add(predecessor);
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

	/**
	 * beware: this is linear-time, if you have the index of node, use it to get the label from the list directly
	 */
	@Override
	public L getOutgoingEdgeLabel(final T node) {
		return mOutgoingEdgeLabels.get(mOutgoingNodes.indexOf(node));
	}

	/**
	 * beware: this is linear-time, if you have the index of node, use it to get the label from the list directly
	 */
	@Override
	public L getIncomingEdgeLabel(final T node) {
		if (node != null) {
			return node.mOutgoingEdgeLabels.get(node.mOutgoingNodes.indexOf(this));
		}
		return null;
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<IWalkable> getSuccessors() {
		return (List<IWalkable>) getOutgoingNodes();
	}

	public List<L> getOutgoingEdgeLabels() {
		return mOutgoingEdgeLabels;
	}

}
