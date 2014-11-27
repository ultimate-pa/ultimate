package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Collection;

public interface IGraph<V, E> {

	Collection<E> getOutgoingEdges(V vertice);

	V getSource(E edge);

	V getTarget(E edge);
}