package de.uni_freiburg.informatik.ultimate.model.structure;

/**
 * This interface describes a modifiable version of a multigraph edge as
 * described in {@link IMultigraphEdge}. The corresponding modifiable node is
 * described through the interface {@link IModifiableExplicitEdgesMultigraph}.
 * 
 * Note that this interface also includes the methods for clients to modify the
 * graph safely, i.e. preventing any unconnected nodes or mismatches between
 * incoming and outgoing lists.
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
 *            <tt>public final class FinalModelEdge implements IModifiableMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge implements IModifiableMultigraphEdge&lt;V,FinalModelNode&gt;</tt>
 *            .
 * @see IMultigraphEdge
 * @see IExplicitEdgesMultigraph
 */
public interface IModifiableMultigraphEdge<V extends IModifiableExplicitEdgesMultigraph<V, E>, E extends IModifiableMultigraphEdge<V, E>>
		extends IMultigraphEdge<V, E> {

	/***
	 * 
	 * This method changes the graph by disconnecting the old target of the
	 * edge: It removes this edge from the incoming list of the old target. Then
	 * it connects the given target by adding this edge to the incoming list of
	 * the given target. It also updates the target in this edge.
	 * 
	 * If the given target is null, this method will do nothing.
	 * 
	 * @param target
	 *            A new target or null
	 */
	void redirectTarget(V target);

	/**
	 * This method changes the graph by disconnecting the old source of the
	 * edge: It removes this edge from the outgoing list of the old source. Then
	 * it connects the given source by adding this edge to the outgoing list of
	 * the given source. It also updates the source in this edge.
	 * 
	 * If the given source is null, this method will do nothing.
	 * 
	 * @param source
	 *            A new source or null
	 */
	void redirectSource(V source);

	/**
	 * This method sets the current target of this edge. It does not change
	 * anything in the nodes of the graph.
	 * 
	 * @param target
	 *            A new target or null.
	 */
	void setTarget(V target);

	/**
	 * This method sets the current source of this edge. It does not change
	 * anything in the nodes of the graph.
	 * 
	 * @param target
	 *            A new source or null.
	 */
	void setSource(V source);

	/**
	 * This method will disconnect the current target of this edge: It removes
	 * this edge from the incoming list of the current target of the edge, then
	 * sets the target of the edge to null.
	 * 
	 * If the current target of this edge is already null, this method will do
	 * nothing.
	 */
	void disconnectTarget();

	/**
	 * This method will disconnect the current source of this edge: It removes
	 * this edge from the outgoing list of the current source of the edge, then
	 * sets the source of the edge to null.
	 * 
	 * If the current source of this edge is already null, this method will do
	 * nothing.
	 */
	void disconnectSource();

}
