package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Collection;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <V>
 * @param <E>
 */
public interface IGraph<V, E> {

	Collection<E> getOutgoingEdges(V vertice);

	V getSource(E edge);

	V getTarget(E edge);
}