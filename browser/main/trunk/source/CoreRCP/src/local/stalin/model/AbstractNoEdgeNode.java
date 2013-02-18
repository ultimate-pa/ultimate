/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	AbstractNode.java created on Nov 18, 2009 by Bj�rn Buchhold
 *
 */
package local.stalin.model;

import java.util.LinkedList;
import java.util.List;

/**
 * AbstractNode
 *
 * @author Björn Buchhold
 *
 */
public abstract class AbstractNoEdgeNode extends AbstractElement implements INode {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -5963278907103525814L;

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addIncomingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean addIncomingEdge(IEdge element) {
		return this.addIncomingNode(element.getSource());
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addIncomingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean addIncomingEdge(INode element) {
		return this.addIncomingNode(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addOutgoingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean addOutgoingEdge(IEdge element) {
		return this.addOutgoingNode(element.getTarget());
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.model.INode#addOutgoingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean addOutgoingEdge(INode element) {
		return this.addOutgoingNode(element);
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getIncomingEdges()
	 */
	@Override
	public List<IEdge> getIncomingEdges() {
		List<IEdge> edges = new LinkedList<IEdge>();
		for (INode src : this.getIncomingNodes()) {
			edges.add(new Edge(src,this));
		}
		return edges;
	}


	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getOutgoingEdges()
	 */
	@Override
	public List<IEdge> getOutgoingEdges() {
		List<IEdge> edges = new LinkedList<IEdge>();
		for (INode target : this.getOutgoingNodes()) {
			edges.add(new Edge(this,target));
		}
		return edges;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeIncomingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean removeIncomingEdge(IEdge element) {
		return this.removeIncomingNode(element.getSource());
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.INode#removeOutgoingEdge(local.stalin.model.IEdge)
	 */
	@Override
	public boolean removeOutgoingEdge(IEdge element) {
		return this.removeOutgoingNode(element.getTarget());
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.model.INode#getChildCount()
	 */
	@Override
	public int getChildCount() {
		return this.getOutgoingNodes().size();
	}


}
