package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * Executes a search on an arbitrary graph using an implementation of A*. Finds
 * a path according to a given heuristic from start to target if one exists.
 * 
 * You can specify edges that should be ignored during the search.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class AStar<V, E> {

	private final Logger mLogger;
	private final IHeuristic<V, E> mHeuristic;
	private final V mStart;
	private final V mTarget;
	private final IEdgeDenier<E> mEdgeDenier;
	private final Map<V, AstarAnnotation<E>> mAnnotation;
	private final IGraph<V, E> mGraph;

	public AStar(Logger logger, V start, V target, IHeuristic<V, E> heuristic, IGraph<V, E> graph) {
		this(logger, start, target, heuristic, graph, new NoEdgeDenier<E>());
	}

	public AStar(Logger logger, V start, V target, IHeuristic<V, E> heuristic, IGraph<V, E> graph,
			Collection<E> forbiddenEdges) {
		this(logger, start, target, heuristic, graph, new CollectionEdgeDenier<>(forbiddenEdges));
	}

	public AStar(Logger logger, V start, V target, IHeuristic<V, E> heuristic, IGraph<V, E> graph,
			IEdgeDenier<E> edgeDenier) {
		mLogger = logger;
		mHeuristic = heuristic;
		mStart = start;
		mTarget = target;
		mEdgeDenier = edgeDenier;
		mGraph = graph;
		mAnnotation = new HashMap<>();
	}

	public List<E> findPath() {
		// check for trivial paths
		for (E outgoing : mGraph.getOutgoingEdges(mStart)) {
			final AstarAnnotation<E> currentAnnotation = getAnnotation(mStart);
			if (mEdgeDenier.isForbidden(outgoing, new BackpointerIterator(currentAnnotation))) {
				continue;
			}

			if (mGraph.getTarget(outgoing).equals(mTarget)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Found trivial path from source " + mStart + " to target " + mTarget + ": "
							+ outgoing);
				}
				return Collections.singletonList(outgoing);
			}
		}

		return astar();
	}

	private List<E> astar() {
		final FasterPriorityQueue<V> open = new FasterPriorityQueue<V>(new Comparator<V>() {
			@Override
			public int compare(V o1, V o2) {
				return Integer.compare(getAnnotation(o1).getExpectedCostToTarget(), getAnnotation(o2)
						.getExpectedCostToTarget());
			}
		});
		final Set<E> closed = new HashSet<E>();

		initialize(mStart, open);

		// paths of length 1 are already found in findPath, so we make one run
		// without checking for the target node
		V currentNode = open.poll();
		expandNode(currentNode, open, closed);

		List<E> path = null;
		while (!open.isEmpty()) {
			currentNode = open.poll();

			if (currentNode.equals(mTarget)) {
				// path found
				path = createPath(currentNode);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("Found path of length %s from source %s to target %s: %s", path.size(),
							mStart, mTarget, Utils.join(path, ", ")));
				}
				break;
			}
			expandNode(currentNode, open, closed);
		}
		if (path == null) {
			mLogger.warn(String.format("Did not find a path from source %s to target %s!", mStart, mTarget));
		}
		return path;
	}

	private void initialize(V node, FasterPriorityQueue<V> open) {
		open.add(node);
		final AstarAnnotation<E> annot = new AstarAnnotation<E>();
		addAnntotation(node, annot);
	}

	private void expandNode(final V currentNode, final FasterPriorityQueue<V> open, final Set<E> closed) {
		for (final E edge : mGraph.getOutgoingEdges(currentNode)) {

			final AstarAnnotation<E> currentAnnotation = getAnnotation(currentNode);
			if (mEdgeDenier.isForbidden(edge, new BackpointerIterator(currentAnnotation))) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("forbidden: " + edge);
				}
				continue;
			}

			final V successor = mGraph.getTarget(edge);
			final AstarAnnotation<E> successorAnnotation = getAnnotation(successor);

			final int costSoFar = currentAnnotation.getCostSoFar() + mHeuristic.getConcreteCost(edge);
			if (open.contains(successor) && costSoFar >= successorAnnotation.getCostSoFar()) {
				// we already know the successor and our current way is not
				// better than the new one
				continue;
			}

			final int expectedCost = costSoFar + mHeuristic.getHeuristicValue(successor, edge, mTarget);

			open.remove(successor);
			successorAnnotation.setExpectedCostToTarget(expectedCost);
			if (successorAnnotation.isLowest()) {
				successorAnnotation.setBackPointer(edge);
				successorAnnotation.setCostSoFar(costSoFar);
				open.add(successor);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Considering [" + edge.hashCode() + "] " + edge + " --> " + successor);
				}
			}
		}

	}

	private List<E> createPath(V target) {
		final List<E> rtr = new ArrayList<E>();
		final Set<AstarAnnotation<E>> closed = new HashSet<>();

		AstarAnnotation<E> currentAnnotation = getAnnotation(target);
		E current = currentAnnotation.getBackPointer();

		// special case: self loop
		if (mGraph.getSource(current) == mGraph.getTarget(current) && mGraph.getSource(current) == mTarget) {
			rtr.add(current);
			closed.add(currentAnnotation);
			return rtr;
		}

		while (current != null) {
			currentAnnotation = getAnnotation(mGraph.getSource(current));
			rtr.add(current);
			if (!closed.add(currentAnnotation)) {
				assert false : "Found cycle in path. This should not happen and is a bug.";
				Collections.reverse(rtr);
				return rtr;
			}
			if (mGraph.getSource(current) == mTarget) {
				break;
			}
			current = currentAnnotation.getBackPointer();
		}

		Collections.reverse(rtr);
		return rtr;
	}

	private void addAnntotation(V node, AstarAnnotation<E> annon) {
		mAnnotation.put(node, annon);
	}

	private AstarAnnotation<E> getAnnotation(V node) {
		AstarAnnotation<E> annot = mAnnotation.get(node);
		if (annot == null) {
			annot = new AstarAnnotation<E>();
			addAnntotation(node, annot);
		}
		return annot;
	}

	private static final class NoEdgeDenier<E> implements IEdgeDenier<E> {
		@Override
		public boolean isForbidden(E edge, Iterator<E> currentTrace) {
			return false;
		}
	}

	private final class BackpointerIterator implements Iterator<E> {

		private AstarAnnotation<E> mAnnotation;

		private BackpointerIterator(AstarAnnotation<E> currentAnnotation) {
			mAnnotation = currentAnnotation;
		}

		@Override
		public boolean hasNext() {
			return mAnnotation != null && mAnnotation.getBackPointer() != null;
		}

		@Override
		public E next() {
			final E current = mAnnotation.getBackPointer();
			if (current == null) {
				throw new NoSuchElementException();
			}
			mAnnotation = getAnnotation(mGraph.getSource(current));
			return current;
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException("remove");
		}
	}
}
