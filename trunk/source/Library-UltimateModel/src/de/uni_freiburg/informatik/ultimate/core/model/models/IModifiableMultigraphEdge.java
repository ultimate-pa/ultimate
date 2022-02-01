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
package de.uni_freiburg.informatik.ultimate.core.model.models;

/**
 * This interface describes a modifiable version of a multigraph edge as described in {@link IMultigraphEdge}. The
 * corresponding modifiable node is described through the interface {@link IModifiableExplicitEdgesMultigraph}.
 * 
 * Note that this interface also includes the methods for clients to modify the graph safely, i.e. preventing any
 * unconnected nodes or mismatches between incoming and outgoing lists.
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-interfaces to specify
 *            a more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge implements IModifiableMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 * 
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-interfaces to specify
 *            a more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge implements IModifiableMultigraphEdge&lt;V,FinalModelNode&gt;</tt> .
 * @see IMultigraphEdge
 * @see IExplicitEdgesMultigraph
 */
public interface IModifiableMultigraphEdge<V extends IModifiableExplicitEdgesMultigraph<V, E, VL, EL, VIS>, E extends IModifiableMultigraphEdge<V, E, VL, EL, VIS>, VL, EL, VIS extends IVisualizable<VIS>>
		extends IMultigraphEdge<V, E, VL, EL, VIS> {

	/***
	 * 
	 * This method changes the graph by disconnecting the old target of the edge: It removes this edge from the incoming
	 * list of the old target. Then it connects the given target by adding this edge to the incoming list of the given
	 * target. It also updates the target in this edge.
	 * 
	 * If the given target is null, this method will do nothing.
	 * 
	 * @param target
	 *            A new target or null
	 */
	void redirectTarget(V target);

	/**
	 * This method changes the graph by disconnecting the old source of the edge: It removes this edge from the outgoing
	 * list of the old source. Then it connects the given source by adding this edge to the outgoing list of the given
	 * source. It also updates the source in this edge.
	 * 
	 * If the given source is null, this method will do nothing.
	 * 
	 * @param source
	 *            A new source or null
	 */
	void redirectSource(V source);

	/**
	 * This method sets the current target of this edge. It does not change anything in the nodes of the graph.
	 * 
	 * @param target
	 *            A new target or null.
	 */
	void setTarget(V target);

	/**
	 * This method sets the current source of this edge. It does not change anything in the nodes of the graph.
	 * 
	 * @param target
	 *            A new source or null.
	 */
	void setSource(V source);

	/**
	 * This method will disconnect the current target of this edge: It removes this edge from the incoming list of the
	 * current target of the edge, then sets the target of the edge to null.
	 * 
	 * If the current target of this edge is already null, this method will do nothing.
	 */
	void disconnectTarget();

	/**
	 * This method will disconnect the current source of this edge: It removes this edge from the outgoing list of the
	 * current source of the edge, then sets the source of the edge to null.
	 * 
	 * If the current source of this edge is already null, this method will do nothing.
	 */
	void disconnectSource();

}
