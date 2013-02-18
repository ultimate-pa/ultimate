package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * Implementation of the basic functionality of ISimpleAST.
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
 * @see ISimpleAST
 * @see BasePayloadContainer
 * 
 */
public abstract class BaseSimpleAST<T extends ISimpleAST<T>> extends
		BasePayloadContainer implements ISimpleAST<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<T> mOutgoingNodes;

	protected BaseSimpleAST() {
		this(null);
	}

	protected BaseSimpleAST(IPayload payload) {
		super(payload);
		mOutgoingNodes = new ArrayList<T>();
	}

	@Override
	public List<T> getOutgoingNodes() {
		return mOutgoingNodes;
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

}


