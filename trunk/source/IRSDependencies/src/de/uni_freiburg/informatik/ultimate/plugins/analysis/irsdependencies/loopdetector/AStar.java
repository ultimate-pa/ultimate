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

	private static final String INDENT = "   ";

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
		final AstarAnnotation<E> currentAnnotation = getAnnotation(mStart);
		for (E edge : mGraph.getOutgoingEdges(mStart)) {
			if (mEdgeDenier.isForbidden(edge, new BackpointerIterator(currentAnnotation))) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Forbidden [" + edge.hashCode() + "] " + edge);
				}
				continue;
			}

			if (mGraph.getTarget(edge).equals(mTarget)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Found trivial path from source " + mStart + " to target " + mTarget + ": " + edge);
				}
				return Collections.singletonList(edge);
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

		open.add(mStart);

		List<E> path = null;
		while (!open.isEmpty()) {
			final V currentNode = open.poll();

			if (currentNode.equals(mTarget)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Found target");
				}
				// path found
				path = createPath(currentNode);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("Found path of length %s from source %s to target %s: %s", path.size(),
							mStart, mTarget, Utils.join(path, ", ")));
				}
				break;
			}
			expandNode(currentNode, open);
		}
		if (path == null) {
			mLogger.warn(String.format("Did not find a path from source %s to target %s!", mStart, mTarget));
		}
		return path;
	}

	private void expandNode(final V currentNode, final FasterPriorityQueue<V> open) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Expanding " + currentNode);
		}
		final Collection<E> outgoingEdges = mGraph.getOutgoingEdges(currentNode);
		final AstarAnnotation<E> currentAnnotation = getAnnotation(currentNode);

		for (final E edge : outgoingEdges) {
			if (mEdgeDenier.isForbidden(edge, new BackpointerIterator(currentAnnotation))) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Forbidden [" + edge.hashCode() + "] " + edge);
				}
				continue;
			}

			final V successor = mGraph.getTarget(edge);
			final AstarAnnotation<E> successorAnnotation = getAnnotation(successor);

			final int costSoFar = currentAnnotation.getCostSoFar() + mHeuristic.getConcreteCost(edge);
			if (open.contains(successor) && costSoFar >= successorAnnotation.getCostSoFar()) {
				// we already know the successor and our current way is not
				// better than the new one
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Not worthy [" + edge.hashCode() + "][" + successorAnnotation.hashCode()
							+ "] " + edge);
				}
				continue;
			}

			final int expectedCost = costSoFar + mHeuristic.getHeuristicValue(successor, edge, mTarget);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(INDENT + "CostSoFar=" + costSoFar + " ExpectedCost " + expectedCost);
			}
			open.remove(successor);
			successorAnnotation.setExpectedCostToTarget(expectedCost);
			// if (successorAnnotation.isLowest()) {
			successorAnnotation.setBackPointers(edge);
			successorAnnotation.setCostSoFar(costSoFar);
			open.add(successor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(INDENT + "Considering [" + edge.hashCode() + "][" + successorAnnotation.hashCode() + "] "
						+ edge + " --> " + successor);
			}
			continue;
			// } else {
			// if (mLogger.isDebugEnabled()) {
			// mLogger.debug(INDENT + "Already closed  [" + edge.hashCode() +
			// "]["
			// + successorAnnotation.hashCode() + "] " + edge + " --> " +
			// successor);
			// }
			// }
		}
	}

	private List<E> createPath(V targetNode) {
		assert targetNode == mTarget;
		final AStar<V, E>.BackpointerIterator iter = new BackpointerIterator(getAnnotation(targetNode));
		final List<E> rtr = new ArrayList<E>();
		while (iter.hasNext()) {
			rtr.add(iter.next());
		}
		Collections.reverse(rtr);
		return rtr;
	}

	private AstarAnnotation<E> getAnnotation(V node) {
		AstarAnnotation<E> annot = mAnnotation.get(node);
		if (annot == null) {
			annot = new AstarAnnotation<E>();
			mAnnotation.put(node, annot);
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
		private Set<E> mClosed;

		private BackpointerIterator(AstarAnnotation<E> currentAnnotation) {
			mAnnotation = currentAnnotation;
			mClosed = new HashSet<E>();
		}

		@Override
		public boolean hasNext() {
			return mAnnotation != null && mAnnotation.getPreEdge() != null
					&& !mClosed.contains(mAnnotation.getPreEdge());
		}

		@Override
		public E next() {
			final E current = mAnnotation.getPreEdge();
			if (current == null) {
				throw new NoSuchElementException();
			}
			if (!mClosed.add(current)) {
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
