package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * Reference implementation of the {@link IModifiableDirectedGraph} interface.
 * 
 * @author dietsch, heizmann@informatik.uni-freiburg.de
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IModifiableDirectedGraph&lt;FinalModel&gt;</tt>
 *            .
 */
public abstract class ModifiableDirectedGraph<T extends IModifiableDirectedGraph<T>>
extends BaseDirectedGraph<T> implements IModifiableDirectedGraph<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/***
	 * This constructor creates a directed graph node without a predecessor and
	 * without a payload.
	 */
	protected ModifiableDirectedGraph() {
		this(null, null);
	}

	/**
	 * This constructor creates a directed graph node without a predecessor but
	 * with a given payload.
	 * 
	 * @param payload
	 *            A given payload or null
	 */
	protected ModifiableDirectedGraph(IPayload payload) {
		this(null, payload);

	}

	/**
	 * This constructor creates a directed graph node with a given predecessor
	 * node but without a payload.
	 * 
	 * @param parent
	 *            A given parent node or null. If the given parent node is not
	 *            null, this node will be added to the parent's list of outgoing
	 *            nodes and the parent will be added to this node's list of
	 *            incoming nodes.
	 */
	protected ModifiableDirectedGraph(T parent) {
		this(parent, null);
	}

	/**
	 * This constructor creates a directed graph node with a given predecessor
	 * node and a given payload.
	 * 
	 * @param parent
	 *            A given parent node or null. If the given parent node is not
	 *            null, this node will be added to the parent's list of outgoing
	 *            nodes and the parent will be added to this node's list of
	 *            incoming nodes.
	 * @param payload
	 *            A given payload or null
	 */
	protected ModifiableDirectedGraph(T parent, IPayload payload) {
		super(parent, payload);
	}
	

	@Override
	public boolean connectIncoming(T predecessor) {
		boolean thisIncomingChanged = addIncoming(predecessor);
		boolean predecessorOutgoingChanged = predecessor.addOutgoing((T) this);
		assert (thisIncomingChanged == predecessorOutgoingChanged);
		return thisIncomingChanged;
	}

	@Override
	public boolean disconnectIncoming(T predecessor) {
		boolean thisIncomingChanged = removeIncoming(predecessor);
		boolean predecessorOutgoingChanged = predecessor.removeOutgoing((T) this);
		assert (thisIncomingChanged == predecessorOutgoingChanged);
		return thisIncomingChanged;
	}

	@Override
	public boolean connectOutgoing(T successor) {
		boolean thisOutgoingChanged = addOutgoing(successor);
		boolean predecessorIncomingChanged = successor.addIncoming((T) this);
		assert (thisOutgoingChanged == predecessorIncomingChanged);
		return thisOutgoingChanged;
	}

	@Override
	public boolean disconnectOutgoing(T successor) {
		boolean thisOutgoingChanged = removeOutgoing(successor);
		boolean predecessorIncomingChanged = successor.removeIncoming((T) this);
		assert (thisOutgoingChanged == predecessorIncomingChanged);
		return thisOutgoingChanged;
	}
	

	/* ---------- IModifiableOutgoing<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addOutgoing(T outgoing) {
		if (outgoing != null) {
			return mOutgoingNodes.add(outgoing);
		}
		return false;
	}

	@Override
	public boolean addOutgoing(int index, T outgoing) {
		int i = mOutgoingNodes.size();
		mOutgoingNodes.add(index, outgoing);
		return i != mOutgoingNodes.size();
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends T> c) {
		boolean rtr = false;
		for (T outgoing : c) {
			rtr = rtr || addOutgoing(outgoing);
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
	public boolean removeOutgoing(Object o) {
		return mOutgoingNodes.remove(o);
	}

	@Override
	public boolean removeAllOutgoing(Collection<?> c) {
		boolean rtr = false;
		for (Object o : c) {
			rtr = rtr || removeOutgoing(o);
		}
		return rtr;
	}

	/* ---------- IModifiableIncoming<IMultigraphEdge> implementation ---------- */

	@Override
	public boolean addIncoming(T incoming) {
		if (incoming != null) {
			return mIncomingNodes.add(incoming);
		}
		return false;
	}

	@Override
	public boolean addIncoming(int index, T incoming) {
		int i = mIncomingNodes.size();
		mIncomingNodes.add(index, incoming);
		return i != mIncomingNodes.size();
	}

	@Override
	public boolean addAllIncoming(Collection<? extends T> c) {
		boolean rtr = false;
		for (T e : c) {
			rtr = rtr || addIncoming(e);
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
	public boolean removeIncoming(Object o) {
		return mIncomingNodes.remove(o);
	}

	@Override
	public boolean removeAllIncoming(Collection<?> c) {
		boolean rtr = false;
		for (Object o : c) {
			rtr = rtr || removeIncoming(o);
		}
		return rtr;
	}
}
