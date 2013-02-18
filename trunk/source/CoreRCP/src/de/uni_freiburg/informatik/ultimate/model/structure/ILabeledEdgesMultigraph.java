package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * This interface describes a directed multigraph with labeled edges. An
 * implementation of this interface represents a node of such a graph.
 * 
 * The interface provides access to the successors as well as the predecessors
 * of the node.
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
 *            The type of the edge labels of the graph.
 * 
 * @author dietsch
 * @see IElement
 * 
 */
public interface ILabeledEdgesMultigraph<T extends ILabeledEdgesMultigraph<T, L>, L>
		extends IElement, IVisualizable, IWalkable {

	/***
	 * The method returns the direct predecessor nodes of the current node of
	 * the multigraph. If there are no predecessors, the method must return an
	 * empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing the direct predecessors of this node.
	 */
	List<T> getIncomingNodes();

	/***
	 * The method returns the direct successor nodes of the current node of the
	 * multigraph. If there are no successors, the method must return an empty
	 * list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing the direct successors of this node.
	 */
	List<T> getOutgoingNodes();

	
	/***
	 * This method returns for a given predecessor node of this node the edge
	 * label of type L. If the given predecessor node has no edge label or the
	 * node is not a direct successor of this node, this method returns null.
	 * 
	 * @param node
	 *            A predecessor node of this node.
	 * @return A object of type L representing an edge label iff the given node
	 *         is (a) a predecessor of this node and (b) has an edge label. Null
	 *         otherwise.
	 */
	L getIncomingEdgeLabel(T node);
	
	/***
	 * This method returns for a given successor node of this node the edge
	 * label of type L. If the given successor node has no edge label or the
	 * node is not a direct successor of this node, this method returns null.
	 * 
	 * @param node
	 *            A successor node of this node.
	 * @return A object of type L representing an edge label iff the given node
	 *         is (a) a successor of this node and (b) has an edge label. Null
	 *         otherwise.
	 */
	L getOutgoingEdgeLabel(T node);

}
