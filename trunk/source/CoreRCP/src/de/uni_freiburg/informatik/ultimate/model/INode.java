package de.uni_freiburg.informatik.ultimate.model;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

/**
 * This is the _OLD_ main interface for all nodes in graphs or trees
 * 
 * It is superseeded by IElement 
 * 
 * @author dietsch / bisser $LastChangedBy: björn buchhold
 */
@Deprecated
public interface INode extends IElement, IWalkable {

	/**
	 * List<INode> getIncomingNodes
	 * 
	 * @return list of all source nodes of incoming edges
	 */
	List<INode> getIncomingNodes();

	/**
	 * List<INode> getOutgoingNodes
	 * 
	 * @return list of all target nodes of outgoing edges
	 */
	List<INode> getOutgoingNodes();

	/**
	 * boolean addOutgoingNode
	 * 
	 * @param element
	 *            the new target node
	 * @return boolean flag showing success
	 */
	boolean addOutgoingNode(INode element);

	/**
	 * boolean addIncomingNode
	 * 
	 * @param element
	 *            the new source node
	 * @return boolean flag showing success
	 */
	boolean addIncomingNode(INode element);

	/**
	 * boolean removeOutgoingNode
	 * 
	 * @param element
	 *            target node of the outgoing edge to remove
	 * @return boolean flag showing success
	 */
	boolean removeOutgoingNode(INode element);

	/**
	 * boolean removeIncomingNode
	 * 
	 * @param element
	 *            the source node of the incoming edge to be removed
	 * @return boolean flag showing success
	 */
	boolean removeIncomingNode(INode element);

	/**
	 * List<IEdge> getIncomingEdges
	 * 
	 * @return list of all incoming edges
	 */
	List<IEdge> getIncomingEdges();

	/**
	 * List<IEdge> getOutgoingEdges
	 * 
	 * @return list of all outgoing edges
	 */
	List<IEdge> getOutgoingEdges();

	/**
	 * boolean addOutgoingEdge
	 * 
	 * @param element
	 *            the edge to be added as outgoing edge
	 * @return boolean flag showing success
	 */
	boolean addOutgoingEdge(IEdge element);

	/**
	 * boolean addIncomingEdge
	 * 
	 * @param element
	 *            the edge to be added as incoming edge
	 * @return boolean flag showing success
	 */
	boolean addIncomingEdge(IEdge element);

	/**
	 * boolean addOutgoingEdge
	 * 
	 * @param target
	 *            the target node of the new edge
	 * @return boolean flag showing success
	 */
	boolean addOutgoingEdge(INode target);

	/**
	 * boolean addIncomingEdge
	 * 
	 * @param src
	 *            the source node of the new edge
	 * @return boolean flag showing success
	 */
	boolean addIncomingEdge(INode src);

	/**
	 * boolean removeOutgoingEdge
	 * 
	 * @param element
	 *            the edge to be removed
	 * @return boolean flag showing success
	 */
	boolean removeOutgoingEdge(IEdge element);

	/**
	 * boolean removeIncomingEdge
	 * 
	 * @param element
	 *            the edge to be removed
	 * @return boolean flag showing success
	 */
	boolean removeIncomingEdge(IEdge element);

	/**
	 * void removeAllIncoming
	 */
	void removeAllIncoming();

	/**
	 * void removeAllOutgoing
	 */
	void removeAllOutgoing();

	/**
	 * int getChildCount
	 * 
	 * @return the number of child nodes
	 */
	int getChildCount();
}
