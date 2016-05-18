/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/**
 * Reference implementation of {@link IMultigraphEdge}. Works together with {@link BaseExplicitEdgesMultigraph}.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge extends BaseMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-classes to specify a
 *            more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge extends BaseExplicitEdgesMultigraph&lt;V,FinalModelNode&gt;</tt> .
 * @see IMultigraphEdge
 * @see BasePayloadContainer
 * @see BaseExplicitEdgesMultigraph
 */
public abstract class BaseMultigraphEdge<V extends IExplicitEdgesMultigraph<V, E, VL, EL, VisualizationNode>, E extends IMultigraphEdge<V, E, VL, EL, VisualizationNode>, VL, EL>
		extends BasePayloadContainer implements IMultigraphEdge<V, E, VL, EL, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected V mSource;

	protected V mTarget;

	/**
	 * Creates a new {@link BaseMultigraphEdge} with a given source and a given target node, but without a payload. Note
	 * that no nodes are changed through the construction of an edge. You have to change them manually.
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
