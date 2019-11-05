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

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;

/***
 * This interface describes a directed graph with unlabeled edges. An implementation of this interface represents a node
 * of such a graph.
 *
 * This interface describes an unmodifiable directed graph, for a modifiable variant see
 * {@link IModifiableDirectedGraph}.
 *
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare <tt>public final class FinalModel implements IDirectedGraph&lt;FinalModel&gt;</tt> .
 * @see IElement
 * @see IModifiableDirectedGraph
 */
public interface IDirectedGraph<T extends IDirectedGraph<T, E>, E extends IVisualizable<E>>
		extends IElement, IWalkable, IVisualizable<E> {

	/***
	 * The method returns the direct predecessor nodes of the current node of the directed graph. If there are no
	 * predecessors, this method must return an empty list.
	 *
	 * This list should be treated as not modifiable. Use it only to iterate or determine size.
	 *
	 * @return A list containing the direct predecessor of the current node.
	 */
	List<T> getIncomingNodes();

	/***
	 * The method returns the direct successor nodes of the current node of the directed graph. If there are no
	 * successors, this method must return an empty list.
	 *
	 * This list should be treated as not modifiable. Use it only to iterate or determine size.
	 *
	 * @return A list containing the direct successors of the current node.
	 */
	List<T> getOutgoingNodes();

	/**
	 * Returns (for instance) the transitive predecessors/successors of this node.
	 * The direction can be specified manually. Some examples for using the {@code direction} parameter:
	 * <ul>
	 * <li> {@code IDirectedGraph::getIncomingNodes} yields the transitive predecessors.
	 * <li> {@code IDirectedGraph::getOutgoingNodes} yields the transitive successors.
	 * <li> {@code n -> {Collection<T> r = new ArrayList<>(); r.addAll(n.getIncomingNodes);
	 *      r.addAll(n.getOutgoingNodes); return r;}} yields the weakly connected component.
	 * </ul>
	 *
	 * @param direction Edge-direction in which to include nodes
	 * @return Transitive nodes in the specified direction (may or may not contain this node itself)
	 *
	 * @see IDirectedGraph#transitiveNodes(Collection, Function) Apply this function to multiple nodes in a single call
	 */
	@SuppressWarnings("unchecked")
	default Set<T> transitiveNodes(final Function<T, Collection<T>> direction) {
		return transitiveNodes(Collections.singleton((T) this), direction);
	}

	/**
	 * Returns (for instance) the transitive predecessors/successors of a group of nodes.
	 * For more information see {@link #transitiveNodes(Function)}.
	 *
	 * @param startingNodes Group of nodes to start from. Equivalent to (but more efficient than)
	 *                      calling {@link #transitiveNodes(Function)} for each node individually
	 *                      and then creating the union of the individual results.
	 * @param direction Edge-direction in which to include nodes
	 * @return Transitive nodes in the specified direction (may or may not contain this node itself)
	 */
	static <N extends IDirectedGraph<N,?>> Set<N> transitiveNodes(
			final Collection<N> startingNodes, final Function<N, Collection<N>> direction) {
		final Set<N> transitiveNodes = new HashSet<>();
		final Queue<N> newNodes = new ArrayDeque<>();
		newNodes.addAll(startingNodes);
		while (!newNodes.isEmpty()) {
			for (final N trans : direction.apply(newNodes.remove())) {
				if (transitiveNodes.add(trans)) {
					newNodes.add(trans);
				}
			}
		}
		return transitiveNodes;
	}
}
