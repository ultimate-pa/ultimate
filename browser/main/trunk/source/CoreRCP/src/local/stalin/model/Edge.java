/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	Edge.java created on Nov 18, 2009 by Björn Buchhold
 *
 */
package local.stalin.model;

/**
 * Edge
 * 
 * Default implementation of {@link IEdge} The edges keeps references to the
 * nodes that are its source and target.
 * 
 * Edges can be constructed with, or without a payload (results in the payload
 * being null)
 * 
 * @author Björn Buchhold
 * 
 */
public class Edge extends AbstractElement implements IEdge {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 9219656346077957049L;

	private INode source;
	private INode target;

	/**
	 * Constructs an Edge with between the provided {@link INode}'s, carrying
	 * the {@link IPayload} passed as parameter
	 * 
	 * @param src
	 *            the source Node
	 * @param target
	 *            the target node
	 * @param payload
	 *            the payload
	 */
	public Edge(INode src, INode target, IPayload payload) {
		this.source = src;
		this.target = target;
		this.payload = payload;
	}

	/**
	 * Constructs an Edge with between the provided {@link INode}'s, carrying
	 * null as {@link IPayload}
	 * 
	 * @param src
	 *            the source Node
	 * @param target
	 *            the target Node
	 */
	public Edge(INode src, INode target) {
		this(src, target, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.model.IEdge#getSource()
	 */
	@Override
	public INode getSource() {
		return this.source;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.model.IEdge#getTarget()
	 */
	@Override
	public INode getTarget() {
		return this.target;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.model.IEdge#setSource(local.stalin.model.INode)
	 */
	@Override
	public void setSource(INode source) {
		this.source = source;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.model.IEdge#setTarget(local.stalin.model.INode)
	 */
	@Override
	public void setTarget(INode target) {
		this.target = target;
	}

}
