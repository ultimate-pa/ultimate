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

import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/**
 * Reference implementation of the {@link IExplicitEdgesMultigraph} interface. Works together with
 * {@link BaseMultigraphEdge}.
 *
 * @author dietsch
 *
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelNode extends BaseExplicitEdgesMultigraph&lt;FinalModelNode,E&gt;</tt> .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding edge type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> and the corresponding edge type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelNode extends BaseExplicitEdgesMultigraph&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 *            .
 * @see BasePayloadContainer
 * @see IExplicitEdgesMultigraph
 * @see IMultigraphEdge
 */
public abstract class BaseExplicitEdgesMultigraph<V extends IExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode>, E extends IMultigraphEdge<V, E, VL, EL, VisualizationNode>, VL, EL>
		extends BasePayloadContainer implements IExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<E> mOutgoingEdges;

	protected List<E> mIncomingEdges;

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without connections to any other node and without
	 * a payload.
	 */
	protected BaseExplicitEdgesMultigraph() {
		this(null, null, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without connections to any other node but with a
	 * given payload.
	 *
	 * @param payload
	 *            The payload for the current node or null.
	 * @see IPayload
	 */
	protected BaseExplicitEdgesMultigraph(final IPayload payload) {
		this(null, null, payload);

	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without a payload. It creates a new
	 * IMultigraphEdge from the given predecessor to the new node and updates the predecessor's outgoing edges and the
	 * new nodes' incoming edges accordingly. The new edge from the given node to the new node is not labeled, i.e. its
	 * payload will be null.
	 *
	 * @param predecessor
	 *            A node that should become the predecessor of this node or null.
	 * @see IMultigraphEdge
	 */
	protected BaseExplicitEdgesMultigraph(final V predecessor) {
		this(predecessor, null, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without a payload. It creates a new
	 * IMultigraphEdge from the given predecessor to the new node and updates the predecessor's outgoing edges and the
	 * new nodes' incoming edges accordingly. The given edge payload is then used for this new edge.
	 *
	 *
	 * @param predecessor
	 *            A node that should become the predecessor of this node or null.
	 * @param edgePayload
	 *            A payload for the edge from the predecessor to the new node or null. If the predecessor is null, this
	 *            payload will be ignored.
	 */
	protected BaseExplicitEdgesMultigraph(final V predecessor, final IPayload edgePayload) {
		this(predecessor, edgePayload, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node with a given payload, creates a new
	 * IMultigraphEdge from the given predecessor to the new node and updates the predecessor's outgoing edges and the
	 * new nodes' incoming edges by inserting a new {@link BaseMultigraphEdge}, and labels the edge from the predecessor
	 * to the new node with a given edge payload.
	 *
	 * @param predecessor
	 *            A node that should become the predecessor of this node or null.
	 * @param edgePayload
	 *            A payload for the edge from the predecessor to the new node or null. If the predecessor is null, this
	 *            payload will be ignored.
	 * @param payload
	 *            A payload for the new node or null.
	 * @see IPayload
	 */
	protected BaseExplicitEdgesMultigraph(final V predecessor, final IPayload edgePayload, final IPayload payload) {
		super(payload);
		mOutgoingEdges = new ArrayList<>();
		mIncomingEdges = new ArrayList<>();
		if (predecessor != null) {
			@SuppressWarnings("unchecked")
			final E e = (E) new BaseMultigraphEdge<V, E, VL, EL>(predecessor, (V) this, payload) {
				private static final long serialVersionUID = 1L;

				@Override
				public EL getLabel() {
					return null;
				}
			};
			predecessor.getOutgoingEdges().add(e);
			mIncomingEdges.add(e);
		}
	}

	@Override
	public List<E> getIncomingEdges() {
		return mIncomingEdges;
	}

	@Override
	public List<E> getOutgoingEdges() {
		return mOutgoingEdges;
	}

	/***
	 * This method returns a fresh list of all direct successor nodes of the current node by iterating over the outgoing
	 * edges of the current node.
	 *
	 * Modifications to this list do not change the graph structure.
	 *
	 * Note: This method was added to preserve compatibility for debug output; remove if not necessary. Do not use this
	 * method for other purposes!
	 *
	 * @return A fresh list containing all direct successor nodes of this node.
	 */
	public List<V> getOutgoingNodes() {
		final ArrayList<V> rtr = new ArrayList<>();
		for (final E e : getOutgoingEdges()) {
			final V target = e.getTarget();
			if (target != null) {
				rtr.add(target);
			}
		}
		return rtr;
	}

	/**
	 * This method returns a fresh list of all direct predecessor nodes of the current node by iterating over the
	 * incoming edges of the current node.
	 *
	 * Modifications to this list do not change the graph structure.
	 *
	 * Note: This method was added to preserve compatibility for debug output; remove if not necessary. Do not use this
	 * method for other purposes!
	 *
	 * @return A fresh list containing all direct predecessor nodes of this node.
	 */
	public List<V> getIncomingNodes() {
		final ArrayList<V> rtr = new ArrayList<>();
		for (final E e : getIncomingEdges()) {
			final V source = e.getSource();
			if (source != null) {
				rtr.add(source);
			}
		}
		return rtr;
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<IWalkable> getSuccessors() {
		return (List<IWalkable>) getOutgoingEdges();
	}

}
