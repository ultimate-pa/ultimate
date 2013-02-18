package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Reference implementation of the {@link IDirectedGraph} interface.
 * 
 * @author dietsch
 * @see IDirectedGraph
 * @see BasePayloadContainer
 * 
 */
public abstract class BaseDirectedGraph<T extends IDirectedGraph<T>> extends
		BasePayloadContainer implements IDirectedGraph<T> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<T> mOutgoingNodes;

	protected List<T> mIncomingNodes;

	/***
	 * This constructor creates a directed graph node without a predecessor and
	 * without a payload.
	 */
	protected BaseDirectedGraph() {
		this(null, null);
	}

	/**
	 * This constructor creates a directed graph node without a predecessor but
	 * with a given payload.
	 * 
	 * @param payload
	 *            A given payload or null
	 */
	protected BaseDirectedGraph(IPayload payload) {
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
	protected BaseDirectedGraph(T parent) {
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
