package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Reference implementation of {@link IModifiableMultigraphEdge}. Works together
 * with {@link ModifiableExplicitEdgesMultigraph}.
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
 *            <tt>public final class FinalModelEdge extends ModifiableMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter
 *            should be used by sub-classes to specify a more restrictive type
 *            and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge extends ModifiableMultigraphEdge&lt;V,FinalModelNode&gt;</tt>
 *            .
 * @see IModifiableMultigraphEdge
 * @see BasePayloadContainer
 * @see ModifiableExplicitEdgesMultigraph
 */
public abstract class ModifiableMultigraphEdge<V extends IModifiableExplicitEdgesMultigraph<V, E>, E extends IModifiableMultigraphEdge<V, E>>
		extends BaseMultigraphEdge<V, E> implements
		IModifiableMultigraphEdge<V, E> {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

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
	protected ModifiableMultigraphEdge(V source, V target) {
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
	protected ModifiableMultigraphEdge(V source, V target, IPayload payload) {
		super(source, target, payload);
	}

	@Override
	public void setTarget(V target) {
		mTarget = target;
	}

	@Override
	public void setSource(V source) {
		mSource = source;
	}

	@Override
	public void disconnectTarget() {
		if (mTarget != null) {
			mTarget.removeIncoming(this);
			mTarget = null;
		}
	}

	@Override
	public void disconnectSource() {
		if (mSource != null) {
			mSource.removeOutgoing(this);
			mSource = null;
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public void redirectTarget(V target) {
		if (target != null) {
			disconnectTarget();
			setTarget(target);
			target.addIncoming((E) this);
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public void redirectSource(V source) {
		if (source != null) {
			disconnectSource();
			setSource(source);
			source.addOutgoing((E) this);
		}
	}

}
