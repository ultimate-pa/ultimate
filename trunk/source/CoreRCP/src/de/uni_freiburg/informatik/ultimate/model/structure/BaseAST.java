package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * Basic implementation of the {@link IAST} interface.
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-classes to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel extends BaseAST&lt;FinalModel&gt;</tt>
 *            .
 * @see IAST
 * @see BaseSimpleAST
 * 
 */
public abstract class BaseAST<T extends IAST<T>> extends BaseSimpleAST<T> implements
		IAST<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected T mParent;

	/**
	 * This constructor creates a BaseAST node without a parent and without
	 * payload.
	 */
	protected BaseAST() {
		this(null, null);
	}

	/**
	 * This constructor creates a BaseAST node without a parent but with a given
	 * payload.
	 * 
	 * @param payload
	 *            A new payload or null.
	 */
	protected BaseAST(IPayload payload) {
		this(null, payload);

	}

	/**
	 * This constructor creates a BaseAST node with a given parent but without a
	 * payload.
	 * 
	 * @param parent
	 */
	protected BaseAST(T parent) {
		this(parent, null);
	}

	/**
	 * This construtor creates a BaseAST node with a given parent and a given
	 * payload. If the parent is not null, this node will be added to the
	 * parent's list of children.
	 * 
	 * @param parent
	 *            A parent node or null.
	 * @param payload
	 *            A new payload or null.
	 */
	@SuppressWarnings("unchecked")
	protected BaseAST(T parent, IPayload payload) {
		super(payload);
		mOutgoingNodes = new ArrayList<T>();
		if (parent != null) {
			mParent = parent;
			parent.getOutgoingNodes().add((T) this);
		}
	}

	@Override
	public T getIncomingNode() {
		return mParent;
	}

}
