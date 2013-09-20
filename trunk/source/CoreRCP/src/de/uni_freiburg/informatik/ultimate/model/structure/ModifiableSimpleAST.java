package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * This class provides a basic implementation for {@link IModifiableSimpleAST}.
 * It uses the standard list operations to provide modifications to the list of
 * successor nodes of {@link ISimpleAST}.
 * 
 * @author dietsch
 * @see IModifiableSimpleAST
 * 
 */
public abstract class ModifiableSimpleAST<T extends IModifiableSimpleAST<T>> extends
		BaseSimpleAST<T> implements IModifiableSimpleAST<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This constructor creates a {@link ModifiableSimpleAST} without a payload.
	 */
	protected ModifiableSimpleAST() {
		this(null);
	}

	/**
	 * This constructor creates a {@link ModifiableSimpleAST} with a given
	 * payload.
	 * 
	 * @param payload
	 *            A payload for the new {@link ModifiableSimpleAST} node or
	 *            null.
	 */
	protected ModifiableSimpleAST(IPayload payload) {
		super(payload);
	}

	/* ---------- IModifiableSimpleAST implementation ---------- */

	@Override
	public boolean addOutgoing(T successorNode) {
		return mOutgoingNodes.add(successorNode);
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
	public boolean addOutgoing(int index, T outgoing) {
		int size = mOutgoingNodes.size();
		mOutgoingNodes.add(index, outgoing);
		return size != mOutgoingNodes.size();
	}

}
