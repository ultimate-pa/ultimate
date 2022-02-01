/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models;

import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/**
 * Reference implementation of {@link IModifiableMultigraphEdge}. Works together with
 * {@link ModifiableExplicitEdgesMultigraph}.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge extends ModifiableMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge extends ModifiableMultigraphEdge&lt;V,FinalModelNode&gt;</tt> .
 * @see IModifiableMultigraphEdge
 * @see BasePayloadContainer
 * @see ModifiableExplicitEdgesMultigraph
 */
public abstract class ModifiableMultigraphEdge<V extends IModifiableExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode>, E extends IModifiableMultigraphEdge<V, E, VL, EL, VisualizationNode>, VL, EL>
		extends BaseMultigraphEdge<V, E, VL, EL> implements IModifiableMultigraphEdge<V, E, VL, EL, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Creates a new {@link BaseMultigraphEdge} with a given source and a given target node, but without a payload. Note
	 * that no nodes are changed through the construction of an edge. You have to change them manually.
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
	 * Creates a new {@link BaseMultigraphEdge} with a given source node, a given target node, and a given payload. Note
	 * that no nodes are changed through the construction of an edge. You have to change them manually.
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

	@SuppressWarnings("unchecked")
	@Override
	public void disconnectTarget() {
		if (mTarget != null) {
			mTarget.removeIncoming((E) this);
			mTarget = null;
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public void disconnectSource() {
		if (mSource != null) {
			mSource.removeOutgoing((E) this);
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
