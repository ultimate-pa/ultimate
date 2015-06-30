package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Iterator;

/**
 * {@link AStar} will only consider edges that are not forbidden during its
 * search. Edges can be forbidden based on the current search context.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <E>
 *            The type of edges Astar is analyzing.
 */
public interface IEdgeDenier<E> {

	/**
	 * Which edge is forbidden?
	 * 
	 * @param edge
	 *            The current edge
	 * @param currentTrace
	 *            An iterator describing the path from the source of the current
	 *            edge to the start of the search
	 * @return true iff this edge should not be considered (it will be as if
	 *         this edge is not in the graph)
	 */
	boolean isForbidden(E edge, Iterator<E> currentTrace);

}
