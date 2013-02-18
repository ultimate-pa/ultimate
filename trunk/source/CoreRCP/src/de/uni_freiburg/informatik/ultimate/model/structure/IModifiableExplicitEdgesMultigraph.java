package de.uni_freiburg.informatik.ultimate.model.structure;

/***
 * This interface describes a modifiable version of a multigraph node as
 * described in {@link IExplicitEdgesMultigraph}. The corresponding modifiable
 * edge is described through the interface {@link IModifiableMultigraphEdge}.
 * 
 * Note that modifications that preserve the graph integrity should be performed
 * through the methods of the {@link IModifiableMultigraphEdge} interface.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelNode implements IModifiableExplicitEdgesMultigraph&lt;FinalModelNode,E&gt;</tt>
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-interfaces to specify a more restrictive
 *            type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the
 *            corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelNode</tt> and the corresponding edge type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelNode implements IModifiableExplicitEdgesMultigraph&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 *            .
 * 
 * @see IExplicitEdgesMultigraph
 * @see IModifiableMultigraphEdge
 * @see IModifiableIncoming
 * @see IModifiableOutgoing
 */
public interface IModifiableExplicitEdgesMultigraph<V extends IModifiableExplicitEdgesMultigraph<V, E>, E extends IModifiableMultigraphEdge<V, E>>
		extends IExplicitEdgesMultigraph<V, E>, IModifiableIncoming<E>,
		IModifiableOutgoing<E> {

}
