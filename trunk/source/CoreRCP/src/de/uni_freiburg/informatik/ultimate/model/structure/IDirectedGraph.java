package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * This interface describes a directed graph with unlabeled edges. An
 * implementation of this interface represents a node of such a graph.
 * 
 * This interface describes an unmodifiable directed graph, for a modifiable
 * variant see {@link IModifiableDirectedGraph}.
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IDirectedGraph&lt;FinalModel&gt;</tt>
 *            .
 * @see IElement
 * @see IModifiableDirectedGraph
 */
public interface IDirectedGraph<T extends IDirectedGraph<T>> extends IElement,
		IWalkable, IVisualizable {

	/***
	 * The method returns the direct predecessor nodes of the current node of
	 * the directed graph. If there are no predecessors, this method must return
	 * an empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing the direct predecessor of the current node.
	 */
	List<T> getIncomingNodes();

	/***
	 * The method returns the direct successor nodes of the current node of the
	 * directed graph. If there are no successors, this method must return an
	 * empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing the direct successors of the current node.
	 */
	List<T> getOutgoingNodes();
}
