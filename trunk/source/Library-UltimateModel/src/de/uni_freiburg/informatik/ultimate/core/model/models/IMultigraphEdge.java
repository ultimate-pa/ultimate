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
package de.uni_freiburg.informatik.ultimate.core.model.models;

/***
 * 
 * @author dietsch
 * 
 * @param <V>
 *            is the type of the nodes of the concrete model. This parameter should be used by sub-interfaces to specify
 *            a more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to the corresponding node type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> and the corresponding node type <tt>FinalModelNode</tt> would declare
 *            <tt>public final class FinalModelEdge implements IMultigraphEdge&lt;FinalModelNode,FinalModelEdge&gt;</tt>
 *            .
 * @param <E>
 *            is the type of the edges of the concrete model. This parameter should be used by sub-interfaces to specify
 *            a more restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type
 *            <tt>FinalModelEdge</tt> would declare
 *            <tt>public final class FinalModelEdge implements IMultigraphEdge&lt;V,FinalModelNode&gt;</tt>.
 * @param <VL>
 *            is the vertex label type (this can also be the actual type)
 * @param <EL>
 *            is the edge label type (this can also be the actual type)
 * @see IExplicitEdgesMultigraph
 */
public interface IMultigraphEdge<V extends IExplicitEdgesMultigraph<V, E, VL, EL, VIS>, E extends IMultigraphEdge<V, E, VL, EL, VIS>, VL, EL, VIS extends IVisualizable<VIS>>
		extends IElement, IWalkable {

	/**
	 * This method returns the source node of this edge, i.e. the edge is directed from the source node to the target
	 * node.
	 * 
	 * @return The source node of the edge or null.
	 */
	V getSource();

	/**
	 * This method returns the target node of this edge, i.e. the edge is directed from the source node to the target
	 * node.
	 * 
	 * @return The target node of the edge or null.
	 */
	V getTarget();

	EL getLabel();

}
