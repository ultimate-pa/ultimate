package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * Basic implementation of the {@link ILabeledEdgesMultigraph} interface.
 * 
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements ILabeledEdgesMultigraph&lt;FinalModel,L&gt;</tt>
 *            .
 * @param <L>
 *            The type of the edge labels.
 * 
 * @author dietsch
 * @see ILabeledEdgesMultigraph
 */
public abstract class BaseLabeledEdgesMultigraph<T extends BaseLabeledEdgesMultigraph<T, L>, L>
		extends BasePayloadContainer implements ILabeledEdgesMultigraph<T, L> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected List<T> mOutgoingNodes;

	protected List<T> mIncomingNodes;

	protected List<L> mOutgoingEdgeLabels;

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without
	 * connections to any other node and without a payload.
	 */
	protected BaseLabeledEdgesMultigraph() {
		this(null, null, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without
	 * connections to any other node but with a given payload.
	 * 
	 * @param payload
	 *            The payload for the current node or null.
	 * @see IPayload
	 */
	protected BaseLabeledEdgesMultigraph(IPayload payload) {
		this(null, null, payload);

	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without a
	 * payload. It modifies a given BaseLabeledEdgesMultigraph node such that it
	 * becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node). The
	 * new edge from the given node to the new node is not labeled.
	 * 
	 * @param parent
	 *            A node that should become the predecessor of this node or
	 *            null.
	 */
	protected BaseLabeledEdgesMultigraph(T parent) {
		this(parent, null, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node without a
	 * payload. It modifies a given BaseLabeledEdgesMultigraph node such that it
	 * becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node). The
	 * new edge from the given node to the new node is labeled with a given edge
	 * label.
	 * 
	 * @param parent
	 *            A node that should become the predecessor of this node or
	 *            null.
	 * @param incomingEdgeLabel
	 *            A label for the edge from the predecessor to the new node or
	 *            null. If the predecessor is null, this label will be ignored.
	 */
	protected BaseLabeledEdgesMultigraph(T parent, L incomingEdgeLabel) {
		this(parent, incomingEdgeLabel, null);
	}

	/***
	 * This constructor creates a new BaseLabeledEdgesMultigraph node with a
	 * given payload, modifies a given BaseLabeledEdgesMultigraph node such that
	 * it becomes a valid predecessor of the current node (and such that this
	 * BaseLabeledEdgesMultigraph node is a valid successor the given node), and
	 * labels the edge from the predecessor to the new node with a given edge
	 * label.
	 * 
	 * @param predecessor
	 *            A node that should become the predecessor of this node or
	 *            null.
	 * @param incomingEdgeLabel
	 *            A label for the edge from the predecessor to the new node or
	 *            null. If the predecessor is null, this label will be ignored.
	 * @param payload
	 *            A payload for the new node or null.
	 * @see IPayload
	 */
	@SuppressWarnings("unchecked")
	protected BaseLabeledEdgesMultigraph(T predecessor, L incomingEdgeLabel,
			IPayload payload) {
		super(payload);
		mOutgoingEdgeLabels = new ArrayList<L>();
		mOutgoingNodes = new ArrayList<T>();
		mIncomingNodes = new ArrayList<T>();
		if (predecessor != null) {
			predecessor.mOutgoingEdgeLabels.add(incomingEdgeLabel);
			predecessor.mOutgoingNodes.add((T) this);
			mIncomingNodes.add(predecessor);
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

	/**
	 * beware: this is linear-time, if you have the index of node, use it to get the label from the list directly
	 */
	@Override
	public L getOutgoingEdgeLabel(T node) {
		return mOutgoingEdgeLabels.get(mOutgoingNodes.indexOf(node));
	}

	/**
	 * beware: this is linear-time, if you have the index of node, use it to get the label from the list directly
	 */
	@Override
	public L getIncomingEdgeLabel(T node) {
		if (node != null) {
			return node.mOutgoingEdgeLabels.get(node.mOutgoingNodes.indexOf(this));
		}
		return null;
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
	
	public List<L> getOutgoingEdgeLabels() {
		return mOutgoingEdgeLabels;
	}

}
