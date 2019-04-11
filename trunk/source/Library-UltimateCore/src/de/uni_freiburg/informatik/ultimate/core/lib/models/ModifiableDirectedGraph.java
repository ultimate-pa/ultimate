/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableDirectedGraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/***
 * Reference implementation of the {@link IModifiableDirectedGraph} interface.
 * 
 * @author dietsch, heizmann@informatik.uni-freiburg.de
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare <tt>public final class FinalModel implements IModifiableDirectedGraph&lt;FinalModel&gt;</tt>
 *            .
 */
public abstract class ModifiableDirectedGraph<T extends IModifiableDirectedGraph<T, VisualizationNode>>
		extends BaseDirectedGraph<T> implements IModifiableDirectedGraph<T, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/***
	 * This constructor creates a directed graph node without a predecessor and without a payload.
	 */
	protected ModifiableDirectedGraph() {
		this(null, null);
	}

	/**
	 * This constructor creates a directed graph node without a predecessor but with a given payload.
	 * 
	 * @param payload
	 *            A given payload or null
	 */
	protected ModifiableDirectedGraph(IPayload payload) {
		this(null, payload);

	}

	/**
	 * This constructor creates a directed graph node with a given predecessor node but without a payload.
	 * 
	 * @param parent
	 *            A given parent node or null. If the given parent node is not null, this node will be added to the
	 *            parent's list of outgoing nodes and the parent will be added to this node's list of incoming nodes.
	 */
	protected ModifiableDirectedGraph(T parent) {
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
	protected ModifiableDirectedGraph(T parent, IPayload payload) {
		super(parent, payload);
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean connectIncoming(T predecessor) {
		final boolean thisIncomingChanged = addIncoming(predecessor);
		final boolean predecessorOutgoingChanged = predecessor.addOutgoing((T) this);
		assert (thisIncomingChanged == predecessorOutgoingChanged);
		return thisIncomingChanged;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean disconnectIncoming(T predecessor) {
		final boolean thisIncomingChanged = removeIncoming(predecessor);
		final boolean predecessorOutgoingChanged = predecessor.removeOutgoing((T) this);
		assert (thisIncomingChanged == predecessorOutgoingChanged);
		return thisIncomingChanged;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean connectOutgoing(T successor) {
		final boolean thisOutgoingChanged = addOutgoing(successor);
		final boolean predecessorIncomingChanged = successor.addIncoming((T) this);
		assert (thisOutgoingChanged == predecessorIncomingChanged);
		return thisOutgoingChanged;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean disconnectOutgoing(T successor) {
		final boolean thisOutgoingChanged = removeOutgoing(successor);
		final boolean predecessorIncomingChanged = successor.removeIncoming((T) this);
		assert (thisOutgoingChanged == predecessorIncomingChanged);
		return thisOutgoingChanged;
	}

	/* ---------- IModifiableOutgoing<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addOutgoing(T outgoing) {
		if (outgoing == this) {
			assert false;
		}
		if (outgoing != null) {
			return mOutgoingNodes.add(outgoing);
		}
		return false;
	}

	@Override
	public boolean addOutgoing(int index, T outgoing) {
		final int i = mOutgoingNodes.size();
		mOutgoingNodes.add(index, outgoing);
		return i != mOutgoingNodes.size();
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends T> c) {
		boolean rtr = false;
		for (final T outgoing : c) {
			rtr |= addOutgoing(outgoing);
		}
		return rtr;
	}

	@Override
	public boolean addAllOutgoing(int index, Collection<? extends T> c) {
		return mOutgoingNodes.addAll(index, c);
	}

	@Override
	public void clearOutgoing() {
		mOutgoingNodes.clear();
	}

	@Override
	public T removeOutgoing(int index) {
		return mOutgoingNodes.remove(index);
	}

	@Override
	public boolean removeOutgoing(T o) {
		return mOutgoingNodes.remove(o);
	}

	@Override
	public boolean removeAllOutgoing(Collection<? extends T> c) {
		boolean rtr = false;
		for (final T o : c) {
			rtr |= removeOutgoing(o);
		}
		return rtr;
	}

	/* ---------- IModifiableIncoming<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addIncoming(T incoming) {
		if (incoming == this) {
			assert false;
		}
		if (incoming != null) {
			return mIncomingNodes.add(incoming);
		}
		return false;
	}

	@Override
	public boolean addIncoming(int index, T incoming) {
		final int i = mIncomingNodes.size();
		mIncomingNodes.add(index, incoming);
		return i != mIncomingNodes.size();
	}

	@Override
	public boolean addAllIncoming(Collection<? extends T> c) {
		boolean rtr = false;
		for (final T e : c) {
			rtr |= addIncoming(e);
		}
		return rtr;
	}

	@Override
	public boolean addAllIncoming(int index, Collection<? extends T> c) {
		return mIncomingNodes.addAll(index, c);
	}

	@Override
	public void clearIncoming() {
		mIncomingNodes.clear();
	}

	@Override
	public T removeIncoming(int index) {
		return mIncomingNodes.remove(index);
	}

	@Override
	public boolean removeIncoming(T o) {
		return mIncomingNodes.remove(o);
	}

	@Override
	public boolean removeAllIncoming(Collection<? extends T> c) {
		boolean rtr = false;
		for (final T o : c) {
			rtr |= removeIncoming(o);
		}
		return rtr;
	}
}
