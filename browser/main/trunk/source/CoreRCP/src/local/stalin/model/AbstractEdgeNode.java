/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	AbstractEdgeNode.java created on Nov 19, 2009 by Björn Buchhold
 *
 */
package local.stalin.model;

import java.util.LinkedList;
import java.util.List;

/**
 * AbstractEdgeNode
 *
 * @author Björn Buchhold
 *
 */
public abstract class AbstractEdgeNode extends AbstractElement implements INode {


	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 6504487443031626268L;


	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addIncomingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean addIncomingNode(INode element) {
		return this.addIncomingEdge(element);
	}


	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addOutgoingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean addOutgoingNode(INode element) {
		return this.addIncomingEdge(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getChildCount()
	 */
	@Override
	public int getChildCount() {
		return this.getOutgoingEdges().size();
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getIncomingNodes()
	 */
	@Override
	public List<INode> getIncomingNodes() {
		List<INode> nodes = new LinkedList<INode>();
		for (IEdge edge : this.getIncomingEdges()) {
			nodes.add(edge.getSource());
		}
		if(nodes.size()==0){
			return null;
		}
		return nodes;
	}


	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getOutgoingNodes()
	 */
	@Override
	public List<INode> getOutgoingNodes() {
		List<INode> nodes = new LinkedList<INode>();
		for (IEdge edge : this.getOutgoingEdges()) {
			nodes.add(edge.getTarget());
		}
		if(nodes.size()==0){
			return null;
		}
		return nodes;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeIncomingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean removeIncomingNode(INode element) {
		for (IEdge edge : this.getIncomingEdges()) {
			if(edge.getSource().equals(element)){
				return this.removeIncomingEdge(edge);
			}
		}
		return false;
	}


	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeOutgoingNode(local.stalin.model.INode)
	 */
	@Override
	public boolean removeOutgoingNode(INode element) {
		for (IEdge edge : this.getOutgoingEdges()) {
			if(edge.getTarget().equals(element)){
				return this.removeOutgoingEdge(edge);
			}
		}
		return false;
	}

}
