package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

public class ModifiableAST<T extends IModifiableAST<T>> extends BaseAST<T>
		implements IModifiableAST<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This constructor creates a {@link ModifiableAST} without a payload and
	 * without a parent.
	 */
	protected ModifiableAST() {
		this(null, null);
	}

	/**
	 * This constructor creates a {@link ModifiableAST} with a given payload and
	 * without a parent.
	 * 
	 * @param payload
	 *            A payload for the new {@link ModifiableAST} node or null.
	 */
	protected ModifiableAST(IPayload payload) {
		this(null, payload);
	}

	/**
	 * This constructor creates a {@link ModifiableAST} node with a given parent
	 * but without a payload.
	 * 
	 * @param parent
	 */
	protected ModifiableAST(T parent) {
		this(parent, null);
	}

	/**
	 * This construtor creates a {@link ModifiableAST} node with a given parent
	 * and a given payload. If the parent is not null, this node will be added
	 * to the parent's list of children.
	 * 
	 * @param parent
	 *            A parent node or null.
	 * @param payload
	 *            A new payload or null.
	 */
	protected ModifiableAST(T parent, IPayload payload) {
		super(parent, payload);
	}

	/* ---------- IModifiableAST implementation ---------- */

	@Override
	public boolean addOutgoing(T outgoing) {
		return mOutgoingNodes.add(outgoing);
	}

	@Override
	public boolean addOutgoing(int index, T outgoing) {
		int size = mOutgoingNodes.size();
		mOutgoingNodes.add(index, outgoing);
		return size != mOutgoingNodes.size();
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends T> c) {
		return mOutgoingNodes.addAll(c);
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
		return mOutgoingNodes.removeAll(c);
	}

	@Override
	public void setIncomingNode(T parent) {
		mParent = parent;
	}

	@Override
	public void redirectParent(T parent) {
		mParent.removeOutgoing(this);
		mParent = parent;
		if (parent != null) {
			if (!parent.getOutgoingNodes().contains(this)) {
				parent.addOutgoing((T) this);
			}
		}

	}

}
