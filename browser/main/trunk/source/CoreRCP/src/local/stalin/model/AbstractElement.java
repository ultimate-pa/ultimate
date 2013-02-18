/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	AbstractElement.java created on Nov 18, 2009 by Björn Buchhold
 *
 */
package local.stalin.model;

/**
 * Abstract class for all elements. Provides getter and setter for the {@link IPayload}
 * every element has and implements the method hasPayload. 
 * 
 * Known subclasses are Edge, AbstractNoEgdeNode, AbstractEdgeNode, DefaultEdgeNode, DefaultNoEdgeNode
 * 
 * Edges are pretty self-explanatory
 * Nodes can be divided in two kinds:
 * 
 * EdgeNodes keep some data structure of Edges and the code in the AbstractEdgeNode class
 * takes care of getter and setters for incoming and outgoing nodes.
 * 
 * NoEdgeNodes keep a data structure of edges and the code in the AbstractNoEdgeNode takes
 * care of dispatching getters and setters for incoming and outgoing edges
 * 
 * The idea is either to use one of the default implementations or extend one of the
 * abstract classes that extend this one. Directly inheriting from this class is possible
 * but at the moment no situation is known where this is actually recommended.
 *
 * @author Björn Buchhold
 *
 */
public class AbstractElement implements IElement {
	
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -7410987234372259155L;
	
	/**
	 * Payload payload
	 */
	IPayload payload;
	
	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#getPayload()
	 */
	@Override
	public IPayload getPayload() {
		return this.payload;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#hasPayload()
	 */
	@Override
	public boolean hasPayload() {
		return this.payload.isValue();
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#setPayload(local.stalin.model.IPayload)
	 */
	@Override
	public void setPayload(IPayload payload) {
		this.payload=payload;
	}

}
