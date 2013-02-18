package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Reference implementation of {@link IMultigraphEdge}. Works together with
 * {@link BaseExplicitEdgesMultigraph}.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter
 *            should be used by sub-classes to specify a more restrictive type
 *            and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the
 *            corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type
 *            <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge extends BaseMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-classes to specify a more restrictive type
 *            and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge extends BaseExplicitEdgesMultigraph&lt;V,FinalModelNode&gt;</tt>
 *            .
 * @see IMultigraphEdge
 * @see BasePayloadContainer
 * @see BaseExplicitEdgesMultigraph
 */
public abstract class BaseMultigraphEdge<V extends IExplicitEdgesMultigraph<V, E>, E extends IMultigraphEdge<V, E>>
		extends BasePayloadContainer implements IMultigraphEdge<V, E> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected V mSource;

	protected V mTarget;

	/**
	 * Creates a new {@link BaseMultigraphEdge} with a given source and a given
	 * target node, but without a payload. Note that no nodes are changed
	 * through the construction of an edge. You have to change them manually.
	 * 
	 * @param source
	 *            The source node or null.
	 * @param target
	 *            The target node or null.
	 */
	protected BaseMultigraphEdge(V source, V target) {
		this(source, target, null);
	}

	/**
	 * Creates a new {@link BaseMultigraphEdge} with a given source node, a
	 * given target node, and a given payload. Note that no nodes are changed
	 * through the construction of an edge. You have to change them manually.
	 * 
	 * @param source
	 *            The source node or null.
	 * @param target
	 *            The target node or null.
	 * @param payload
	 *            A payload or null.
	 */
	protected BaseMultigraphEdge(V source, V target, IPayload payload) {
		super(payload);
		mSource = source;
		mTarget = target;
	}

	@Override
	public V getSource() {
		return mSource;
	}

	@Override
	public V getTarget() {
		return mTarget;
	}

	@Override
	public List<IWalkable> getSuccessors() {
		return Collections.singletonList((IWalkable) mTarget);
	}

}
