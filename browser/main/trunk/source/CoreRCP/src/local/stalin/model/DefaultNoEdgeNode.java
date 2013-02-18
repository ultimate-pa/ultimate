/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	DefaultNoEdgeNode.java created on Nov 26, 2009 by Björn Buchhold
 *
 */
package local.stalin.model;

import java.util.ArrayList;
import java.util.List;

/**
 * DefaultNoEdgeNode
 *
 * @author Björn Buchhold
 *
 */
public class DefaultNoEdgeNode extends AbstractNoEdgeNode {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8289673298976654612L;
	private List<INode> incoming = new ArrayList<INode>();
	private List<INode> outgoing = new ArrayList<INode>();
	
	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addIncomingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean addIncomingNode(INode element) {
		return this.incoming.add(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addOutgoingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean addOutgoingNode(INode element) {
		return this.outgoing.add(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getIncomingNodes()
	 */
	@Override
	public List<INode> getIncomingNodes() {
		return this.incoming;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getOutgoingNodes()
	 */
	@Override
	public List<INode> getOutgoingNodes() {
		return this.outgoing;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeAllIncoming()
	 */
	@Override
	public void removeAllIncoming() {
		this.incoming.clear();
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeAllOutgoing()
	 */
	@Override
	public void removeAllOutgoing() {
		this.outgoing.clear();
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeIncomingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean removeIncomingNode(INode element) {
		return this.incoming.remove(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeOutgoingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean removeOutgoingNode(INode element) {
		return this.outgoing.remove(element);
	}

}
