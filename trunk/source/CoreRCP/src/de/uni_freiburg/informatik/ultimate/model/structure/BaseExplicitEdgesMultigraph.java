package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Reference implementation of the {@link IExplicitEdgesMultigraph} interface.
 * Works together with {@link BaseMultigraphEdge}.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter
 *            should be used by sub-classes to specify a more restrictive type
 *            and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelNode extends BaseExplicitEdgesMultigraph&lt;FinalModelNode,E&gt;</tt>
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-classes to specify a more restrictive type
 *            and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the
 *            corresponding edge type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> and the corresponding edge type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelNode extends BaseExplicitEdgesMultigraph&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 *            .
 * @see BasePayloadContainer
 * @see IExplicitEdgesMultigraph
 * @see IMultigraphEdge
 */
public abstract class BaseExplicitEdgesMultigraph<V extends IExplicitEdgesMultigraph<V, E>, E extends IMultigraphEdge<V, E>>
		extends BasePayloadContainer implements IExplicitEdgesMultigraph<V, E> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<E> mOutgoingEdges;

	protected List<E> mIncomingEdges;

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without
	 * connections to any other node and without a payload.
	 */
	protected BaseExplicitEdgesMultigraph() {
		this(null, null, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without
	 * connections to any other node but with a given payload.
	 * 
	 * @param payload
	 *            The payload for the current node or null.
	 * @see IPayload
	 */
	protected BaseExplicitEdgesMultigraph(IPayload payload) {
		this(null, null, payload);

	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without a
	 * payload. It creates a new IMultigraphEdge from the given predecessor to
	 * the new node and updates the predecessor's outgoing edges and the new
	 * nodes' incoming edges accordingly. The new edge from the given node to
	 * the new node is not labeled, i.e. its payload will be null.
	 * 
	 * @param predecessor
	 *            A node that should become the predecessor of this node or
	 *            null.
	 * @see IMultigraphEdge
	 */
	protected BaseExplicitEdgesMultigraph(V predecessor) {
		this(predecessor, null, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node without a
	 * payload. It creates a new IMultigraphEdge from the given predecessor to
	 * the new node and updates the predecessor's outgoing edges and the new
	 * nodes' incoming edges accordingly. The given edge payload is then used
	 * for this new edge.
	 * 
	 * 
	 * @param predecessor
	 *            A node that should become the predecessor of this node or
	 *            null.
	 * @param edgePayload
	 *            A payload for the edge from the predecessor to the new node or
	 *            null. If the predecessor is null, this payload will be
	 *            ignored.
	 */
	protected BaseExplicitEdgesMultigraph(V predecessor, IPayload edgePayload) {
		this(predecessor, edgePayload, null);
	}

	/***
	 * This constructor creates a new BaseExplicitEdgesMultigraph node with a
	 * given payload, creates a new IMultigraphEdge from the given predecessor
	 * to the new node and updates the predecessor's outgoing edges and the new
	 * nodes' incoming edges by inserting a new {@link BaseMultigraphEdge}, and
	 * labels the edge from the predecessor to the new node with a given edge
	 * payload.
	 * 
	 * @param predecessor
	 *            A node that should become the predecessor of this node or
	 *            null.
	 * @param edgePayload
	 *            A payload for the edge from the predecessor to the new node or
	 *            null. If the predecessor is null, this payload will be
	 *            ignored.
	 * @param payload
	 *            A payload for the new node or null.
	 * @see IPayload
	 */
	protected BaseExplicitEdgesMultigraph(V predecessor, IPayload edgePayload,
			IPayload payload) {
		super(payload);
		mOutgoingEdges = new ArrayList<E>();
		mIncomingEdges = new ArrayList<E>();
		if (predecessor != null) {
			@SuppressWarnings("unchecked")
			E e = (E) new BaseMultigraphEdge<V, E>(predecessor, (V) this,
					payload){
						private static final long serialVersionUID = 1L;
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
	 * This method returns a fresh list of all direct successor nodes of the
	 * current node by iterating over the outgoing edges of the current node.
	 * 
	 * Modifications to this list do not change the graph structure.
	 * 
	 * Note: This method was added to preserve compatibility for debug output;
	 * remove if not necessary. Do not use this method for other purposes!
	 * 
	 * @return A fresh list containing all direct successor nodes of this node.
	 */
	public List<V> getOutgoingNodes() {
		ArrayList<V> rtr = new ArrayList<V>();
		for (E e : mOutgoingEdges) {
			V target = e.getTarget();
			if(target != null){
				rtr.add(target);				
			}
		}
		return rtr;
	}

	/**
	 * This method returns a fresh list of all direct predecessor nodes of the
	 * current node by iterating over the incoming edges of the current node.
	 * 
	 * Modifications to this list do not change the graph structure.
	 * 
	 * Note: This method was added to preserve compatibility for debug output;
	 * remove if not necessary. Do not use this method for other purposes!
	 * 
	 * @return A fresh list containing all direct predecessor nodes of this
	 *         node.
	 */
	public List<V> getIncomingNodes() {
		ArrayList<V> rtr = new ArrayList<V>();
		for (E e : getIncomingEdges()) {
			V source = e.getSource();
			if(source != null){
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
