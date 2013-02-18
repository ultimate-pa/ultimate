package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the
 *            corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type
 *            <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge implements IMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge implements IMultigraphEdge&lt;V,FinalModelNode&gt;</tt>
 *            .
 */
public interface IMultigraphEdge<V extends IExplicitEdgesMultigraph<V, E>, E extends IMultigraphEdge<V, E>>
		extends IElement, IWalkable {

	/**
	 * This method returns the source node of this edge, i.e. the edge is
	 * directed from the source node to the target node.
	 * 
	 * @return The source node of the edge or null.
	 */
	V getSource();

	/**
	 * This method returns the target node of this edge, i.e. the edge is
	 * directed from the source node to the target node.
	 * 
	 * @return The target node of the edge or null.
	 */
	V getTarget();

}
