package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 * @param <V>
 *            Type of vertices
 * @param <E>
 *            Type of edges
 */
public interface IHeuristic<V, E> {
	int getHeuristicValue(V from, V to);

	int getConcreteCost(E e);
}