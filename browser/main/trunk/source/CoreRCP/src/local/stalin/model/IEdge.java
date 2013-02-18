package local.stalin.model;

/**
 * IEdge
 * 
 * Basic Edge interface. Edges have source and target nodes (INode).
 * The default implementation is {@link Edge}.
 *
 * @author Björn Buchhold
 *
 */
public interface IEdge extends IElement {

	/**
	 * INode getTarget
	 * @return the target node
	 */
	INode getTarget();
	
	/**
	 * INode getSource
	 * @return the source node
	 */
	INode getSource();
	
	/**
	 * void setTarget
	 * @param target the target node
	 */
	void setTarget(INode target);
	
	/**
	 * void setSource
	 * @param source the source node
	 */
	void setSource(INode source);
}
