package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * This interface describes an unmodifiable directed graph with unlabeled edges.
 * An implementation of this interface represents a node of such a graph.
 * 
 * 
 * @author dietsch, heizmann@informatik.uni-freiburg.de
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IModifiableDirectedGraph&lt;FinalModel&gt;</tt>
 *            .
 * @see IElement
 * @see IModifiableDirectedGraph
 */
public interface IModifiableDirectedGraph<T extends IModifiableDirectedGraph<T>> extends IDirectedGraph<T>,
		IWalkable, IVisualizable, IModifiableIncoming<T>, IModifiableOutgoing<T> {

	/**
	 * Add predecessor such that the graph invariant (node b is outgoing node
	 * of node a iff node a is incoming node of node b) is preserved.
	 * 
	 * @return true if the incoming nodes where changed as a result of the call 
	 */
	boolean connectIncoming(T predecessor);
	
	/**
	 * Add predecessor such that the graph invariant (node b is outgoing node
	 * of node a iff node a is incoming node of node b) is preserved.
	 * 
	 * @return true if the incoming nodes where changed as a result of the call 
	 */
	boolean disconnectIncoming(T predecessor);

	
	
	/**
	 * Add successor such that the graph invariant (node b is outgoing node
	 * of node a iff node a is incoming node of node b) is preserved.
	 * 
	 * @return true if the incoming nodes where changed as a result of the call 
	 */
	boolean connectOutgoing(T predecessor);
	
	/**
	 * Add successor such that the graph invariant (node b is outgoing node
	 * of node a iff node a is incoming node of node b) is preserved.
	 * 
	 * @return true if the incoming nodes where changed as a result of the call 
	 */
	boolean disconnectOutgoing(T predecessor);

}
