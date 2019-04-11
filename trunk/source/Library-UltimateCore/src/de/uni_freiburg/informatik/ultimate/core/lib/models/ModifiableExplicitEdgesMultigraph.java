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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/***
 * This class is the reference implementation for {@link IModifiableExplicitEdgesMultigraph}. It works together with
 * {@link ModifiableMultigraphEdge}.
 * 
 * @author dietsch
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelNode extends ModifiableExplicitEdgesMultigraph&lt;FinalModelNode,E&gt;</tt>
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> and the corresponding edge type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelNode extends ModifiableExplicitEdgesMultigraph&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * @see IModifiableExplicitEdgesMultigraph
 * @see BaseExplicitEdgesMultigraph
 * @see ModifiableMultigraphEdge
 */
public abstract class ModifiableExplicitEdgesMultigraph<V extends IModifiableExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode>, E extends IModifiableMultigraphEdge<V, E, VL, EL, VisualizationNode>, VL, EL>
		extends BaseExplicitEdgesMultigraph<V, E, VL, EL>
		implements IModifiableExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/***
	 * This constructor creates a new ModifiableExplicitEdgesMultigraph node without connections to any other node and
	 * without a payload.
	 */
	protected ModifiableExplicitEdgesMultigraph() {
		this(null, null, null);
	}

	/***
	 * This constructor creates a new ModifiableExplicitEdgesMultigraph node without connections to any other node but
	 * with a given payload.
	 * 
	 * @param payload
	 *            The payload for the current node or null.
	 * @see IPayload
	 */
	protected ModifiableExplicitEdgesMultigraph(IPayload payload) {
		this(null, null, payload);

	}

	/***
	 * This constructor creates a new ModifiableExplicitEdgesMultigraph node without a payload. It creates a new
	 * IMultigraphEdge from the given predecessor to the new node and updates the predecessor's outgoing edges and the
	 * new nodes' incoming edges accordingly. The new edge from the given node to the new node is not labeled, i.e. its
	 * payload will be null.
	 * 
	 * @param predecessor
	 *            A node that should become the predecessor of this node or null.
	 * @see IMultigraphEdge
	 */
	protected ModifiableExplicitEdgesMultigraph(V predecessor) {
		this(predecessor, null, null);
	}

	/***
	 * This constructor creates a new ModifiableExplicitEdgesMultigraph node without a payload. It creates a new
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
	protected ModifiableExplicitEdgesMultigraph(V predecessor, IPayload edgePayload) {
		this(predecessor, edgePayload, null);
	}

	/***
	 * This constructor creates a new ModifiableExplicitEdgesMultigraph node with a given payload, creates a new
	 * IMultigraphEdge from the given predecessor to the new node and updates the predecessor's outgoing edges and the
	 * new nodes' incoming edges accordingly, and labels the edge from the predecessor to the new node with a given edge
	 * payload.
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
	protected ModifiableExplicitEdgesMultigraph(V predecessor, IPayload edgePayload, IPayload payload) {
		super(predecessor, edgePayload, payload);
	}

	/* ---------- IModifiableOutgoing<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addOutgoing(E outgoing) {
		if (outgoing != null) {
			assert outgoing.getSource() == this;
			return mOutgoingEdges.add(outgoing);
		}
		return false;
	}

	@Override
	public boolean addOutgoing(int index, E outgoing) {
		final int i = mOutgoingEdges.size();
		mOutgoingEdges.add(index, outgoing);
		return i != mOutgoingEdges.size();
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends E> c) {
		boolean rtr = false;
		for (final E outgoing : c) {
			rtr |= addOutgoing(outgoing);
		}
		return rtr;
	}

	@Override
	public boolean addAllOutgoing(int index, Collection<? extends E> c) {
		return mOutgoingEdges.addAll(index, c);
	}

	@Override
	public void clearOutgoing() {
		mOutgoingEdges.clear();
	}

	@Override
	public E removeOutgoing(int index) {
		return mOutgoingEdges.remove(index);
	}

	@Override
	public boolean removeOutgoing(E o) {
		return mOutgoingEdges.remove(o);
	}

	@Override
	public boolean removeAllOutgoing(Collection<? extends E> c) {
		boolean rtr = false;
		for (final E o : c) {
			rtr |= removeOutgoing(o);
		}
		return rtr;
	}

	/* ---------- IModifiableIncoming<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addIncoming(E incoming) {
		if (incoming != null) {
			assert incoming.getTarget() == this;
			return mIncomingEdges.add(incoming);
		}
		return false;
	}

	@Override
	public boolean addIncoming(int index, E incoming) {
		final int i = mIncomingEdges.size();
		mIncomingEdges.add(index, incoming);
		return i != mIncomingEdges.size();
	}

	@Override
	public boolean addAllIncoming(Collection<? extends E> c) {
		boolean rtr = false;
		for (final E e : c) {
			rtr |= addIncoming(e);
		}
		return rtr;
	}

	@Override
	public boolean addAllIncoming(int index, Collection<? extends E> c) {
		return mIncomingEdges.addAll(index, c);
	}

	@Override
	public void clearIncoming() {
		mIncomingEdges.clear();
	}

	@Override
	public E removeIncoming(int index) {
		return mIncomingEdges.remove(index);
	}

	@Override
	public boolean removeIncoming(E o) {
		return mIncomingEdges.remove(o);
	}

	@Override
	public boolean removeAllIncoming(Collection<? extends E> c) {
		boolean rtr = false;
		for (final E o : c) {
			rtr |= removeIncoming(o);
		}
		return rtr;
	}
}
