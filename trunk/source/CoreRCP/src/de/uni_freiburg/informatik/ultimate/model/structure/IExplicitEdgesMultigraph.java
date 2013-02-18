package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * This interface describes models that represent a multi-graph structure, i.e.
 * a graph with possibly multiple directed edges between two nodes. The
 * interface requires that the edges of such a multigraph have to be represented
 * by separate objects described by the {@link IMultigraphEdge} interface.
 * 
 * For a multigraph without explicit edges see {@link ILabeledEdgesMultigraph}.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelNode implements IExplicitEdgesMultigraph&lt;FinalModelNode,E&gt;</tt>
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the
 *            corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> and the corresponding edge type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelNode implements IExplicitEdgesMultigraph&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 *            .
 * 
 * @see IElement
 * @see IMultigraphEdge
 * @see IVisualizable
 * @see IWalkable
 */
public interface IExplicitEdgesMultigraph<V extends IExplicitEdgesMultigraph<V, E>, E extends IMultigraphEdge<V, E>>
		extends IElement, IVisualizable, IWalkable {

	/***
	 * The method returns all edges between immediate predecessors of the
	 * current node and the current node, i.e. edges that are directed at the
	 * current node. If there are no such edges, this method must return an
	 * empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing all edges between the direct predecessors of
	 *         the current node and the current node.
	 */
	List<E> getIncomingEdges();

	/***
	 * The method returns all edges between immediate successors of the current
	 * node and the current node, i.e. edges that lead away from the current
	 * node. If there are no such edges, this method must return an empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing all edges between the direct successors of the
	 *         current node and the current node.
	 */
	List<E> getOutgoingEdges();
}
