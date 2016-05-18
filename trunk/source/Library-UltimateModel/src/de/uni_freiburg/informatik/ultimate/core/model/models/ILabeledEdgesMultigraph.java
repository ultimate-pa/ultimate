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

import java.util.List;

/***
 * This interface describes a directed multigraph with labeled edges. An implementation of this interface represents a
 * node of such a graph.
 * 
 * The interface provides access to the successors as well as the predecessors of the node.
 * 
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare
 *            <tt>public final class FinalModel implements ILabeledEdgesMultigraph&lt;FinalModel,L&gt;</tt> .
 * @param <L>
 *            The type of the edge labels of the graph. If this graph should serve as a "real" multigraph, one should
 *            use a Collection as label type.
 * 
 * @author dietsch
 * @see IElement
 * 
 */
public interface ILabeledEdgesMultigraph<T extends ILabeledEdgesMultigraph<T, L, E>, L, E extends IVisualizable<E>>
		extends IElement, IVisualizable<E>, IWalkable {

	/***
	 * The method returns the direct predecessor nodes of the current node of the multigraph. If there are no
	 * predecessors, the method must return an empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or determine size.
	 * 
	 * @return A list containing the direct predecessors of this node.
	 */
	List<T> getIncomingNodes();

	/***
	 * The method returns the direct successor nodes of the current node of the multigraph. If there are no successors,
	 * the method must return an empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or determine size.
	 * 
	 * @return A list containing the direct successors of this node.
	 */
	List<T> getOutgoingNodes();

	/***
	 * This method returns for a given predecessor node of this node the edge label of type L. If the given predecessor
	 * node has no edge label or the node is not a direct successor of this node, this method returns null.
	 * 
	 * @param node
	 *            A predecessor node of this node.
	 * @return A object of type L representing an edge label iff the given node is (a) a predecessor of this node and
	 *         (b) has an edge label. Null otherwise.
	 */
	L getIncomingEdgeLabel(T node);

	/***
	 * This method returns for a given successor node of this node the edge label of type L. If the given successor node
	 * has no edge label or the node is not a direct successor of this node, this method returns null.
	 * 
	 * @param node
	 *            A successor node of this node.
	 * @return A object of type L representing an edge label iff the given node is (a) a successor of this node and (b)
	 *         has an edge label. Null otherwise.
	 */
	L getOutgoingEdgeLabel(T node);

}
