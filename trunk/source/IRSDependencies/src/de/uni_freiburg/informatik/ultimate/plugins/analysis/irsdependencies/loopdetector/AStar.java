/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 *
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
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

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashedPriorityQueue;

/**
 * Executes a search on an arbitrary graph using an implementation of A*. Finds a path according to a given heuristic
 * from start to target if one exists.
 *
 * You can specify edges that should be ignored during the search.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class AStar<V, E> {

	private static final String INDENT = "   ";

	private final ILogger mLogger;
	private final IHeuristic<V, E> mHeuristic;
	private final V mStart;
	private final V mTarget;
	private final IEdgeDenier<E> mEdgeDenier;
	private final IGraph<V, E> mGraph;
	private final IProgressAwareTimer mTimer;

	public AStar(final ILogger logger, final V start, final V target, final IHeuristic<V, E> heuristic,
			final IGraph<V, E> graph, final IProgressAwareTimer timer) {
		this(logger, start, target, heuristic, graph, new NoEdgeDenier<E>(), timer);
	}

	public AStar(final ILogger logger, final V start, final V target, final IHeuristic<V, E> heuristic,
			final IGraph<V, E> graph, final Collection<E> forbiddenEdges, final IProgressAwareTimer timer) {
		this(logger, start, target, heuristic, graph, new CollectionEdgeDenier<>(forbiddenEdges), timer);
	}

	public AStar(final ILogger logger, final V start, final V target, final IHeuristic<V, E> heuristic,
			final IGraph<V, E> graph, final IEdgeDenier<E> edgeDenier, final IProgressAwareTimer timer) {
		mLogger = logger;
		mHeuristic = heuristic;
		mStart = start;
		mTarget = target;
		mEdgeDenier = edgeDenier;
		mGraph = graph;
		mTimer = timer;
	}

	public List<E> findPath() {
		// create initial item
		final OpenItem<V, E> initialOpenItem = createInitialSuccessorItem(mStart);

		// check for trivial paths
		for (final E edge : mGraph.getOutgoingEdges(mStart)) {
			if (mEdgeDenier.isForbidden(edge, new BackpointerIterator(initialOpenItem.getAnnotation()))) {
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

		return astar(initialOpenItem);
	}

	private List<E> astar(final OpenItem<V, E> initialOpenItem) {
		final HashedPriorityQueue<OpenItem<V, E>> open = new HashedPriorityQueue<>(new Comparator<OpenItem<V, E>>() {
			@Override
			public int compare(final OpenItem<V, E> o1, final OpenItem<V, E> o2) {
				return Integer.compare(o1.getAnnotation().getExpectedCostToTarget(),
						o2.getAnnotation().getExpectedCostToTarget());
			}
		});

		// we want to allow that we find paths from start to target when start
		// == target
		// for this, we run the algorithm one time without the check if we
		// reached the target
		open.add(initialOpenItem);
		expandNode(open.poll(), open);

		List<E> path = null;
		while (!open.isEmpty()) {
			checkTimeout();
			final OpenItem<V, E> currentItem = open.poll();

			if (currentItem.getNode().equals(mTarget)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Found target");
				}
				// path found
				path = createPath(currentItem);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("Found path of length %s from source %s to target %s: %s", path.size(),
							mStart, mTarget, CoreUtil.join(path, ", ")));
				}
				break;
			}
			expandNode(currentItem, open);
		}
		if (path == null) {
			mLogger.warn(String.format("Did not find a path from source %s to target %s!", mStart, mTarget));
		}
		return path;
	}

	private void checkTimeout() {
		if (!mTimer.continueProcessing()) {
			mLogger.warn("Received timeout, aborting AStar engine");
			throw new ToolchainCanceledException(getClass());
		}
	}

	private void expandNode(final OpenItem<V, E> currentItem, final HashedPriorityQueue<OpenItem<V, E>> open) {
		final V currentNode = currentItem.getNode();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Expanding " + currentNode);
		}
		final Collection<E> outgoingEdges = mGraph.getOutgoingEdges(currentNode);
		final AstarAnnotation<E> currentAnnotation = currentItem.getAnnotation();

		for (final E nextEdge : outgoingEdges) {
			if (mEdgeDenier.isForbidden(nextEdge, new BackpointerIterator(currentAnnotation))) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Forbidden [" + nextEdge.hashCode() + "] " + nextEdge);
				}
				continue;
			}

			final V successor = mGraph.getTarget(nextEdge);
			final OpenItem<V, E> successorItem = createSuccessorItem(currentItem, nextEdge);
			final AstarAnnotation<E> successorAnnotation = successorItem.getAnnotation();

			final int costSoFar = currentAnnotation.getCostSoFar() + mHeuristic.getConcreteCost(nextEdge);
			if (open.contains(successorItem) && costSoFar >= successorAnnotation.getCostSoFar()) {
				// we already know the successor and our current way is not
				// better than the new one
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Not worthy [" + nextEdge.hashCode() + "][" + successorAnnotation.hashCode()
							+ "] " + nextEdge);
				}
				continue;
			}

			final int expectedCost = costSoFar + mHeuristic.getHeuristicValue(successor, nextEdge, mTarget);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(INDENT + "CostSoFar=" + costSoFar + " ExpectedCost " + expectedCost);
			}
			open.remove(successorItem);
			successorAnnotation.setExpectedCostToTarget(expectedCost);
			if (successorAnnotation.isLowest()) {
				successorAnnotation.setBackPointers(nextEdge, currentAnnotation);
				successorAnnotation.setCostSoFar(costSoFar);
				open.add(successorItem);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Considering [" + nextEdge.hashCode() + "][" + successorAnnotation.hashCode()
							+ "] " + nextEdge + " --> " + successor);
				}
				continue;
			} else {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(INDENT + "Already closed  [" + nextEdge.hashCode() + "]["
							+ successorAnnotation.hashCode() + "] " + nextEdge + " --> " + successor);
				}
			}
		}
	}

	private List<E> createPath(final OpenItem<V, E> currentItem) {
		assert currentItem.getNode() == mTarget;
		final AStar<V, E>.BackpointerIterator iter = new BackpointerIterator(currentItem.getAnnotation());
		final List<E> rtr = new ArrayList<>();
		while (iter.hasNext()) {
			rtr.add(iter.next());
		}
		Collections.reverse(rtr);
		return rtr;
	}

	private OpenItem<V, E> createSuccessorItem(final OpenItem<V, E> current, final E successor) {
		final V target = mGraph.getTarget(successor);
		if (current == null) {
			final Map<V, AstarAnnotation<E>> map = new HashMap<>();
			final V source = mGraph.getSource(successor);
			map.put(source, new AstarAnnotation<E>());
			map.put(target, new AstarAnnotation<E>());
			return new OpenItem<>(target, map);
		}

		final OpenItem<V, E> rtr = new OpenItem<>(target, current);
		if (mGraph.beginScope(successor)) {
			rtr.getAnnotations().beginScope();
		} else if (mGraph.endScope(successor)) {
			if (rtr.getAnnotations().getScopesCount() == 0) {
				mLogger.warn("Allowing successor \"" + successor
						+ "\" although there is no preceeding beginScope (e.g., a call) on this path");
			} else {
				rtr.getAnnotations().endScope();
			}
		}
		AstarAnnotation<E> annot = rtr.getAnnotations().get(target);
		if (annot == null) {
			annot = new AstarAnnotation<>();
			rtr.getAnnotations().put(target, annot);
		}
		return rtr;
	}

	private OpenItem<V, E> createInitialSuccessorItem(final V initialNode) {
		final Map<V, AstarAnnotation<E>> map = new HashMap<>();
		map.put(initialNode, new AstarAnnotation<E>());
		return new OpenItem<>(initialNode, map);
	}

	private static final class NoEdgeDenier<E> implements IEdgeDenier<E> {
		@Override
		public boolean isForbidden(final E edge, final Iterator<E> currentTrace) {
			return false;
		}
	}

	private final class BackpointerIterator implements Iterator<E> {

		private AstarAnnotation<E> mAnnotation;
		private final Set<AstarAnnotation<E>> mClosed;

		private BackpointerIterator(final AstarAnnotation<E> currentAnnotation) {
			mAnnotation = currentAnnotation;
			mClosed = new HashSet<>();
		}

		@Override
		public boolean hasNext() {
			return mAnnotation != null && mAnnotation.getEdge() != null && !mClosed.contains(mAnnotation);
		}

		@Override
		public E next() {
			final E current = mAnnotation.getEdge();
			if (current == null) {
				throw new NoSuchElementException();
			}
			if (!mClosed.add(mAnnotation)) {
				throw new NoSuchElementException();
			}
			mAnnotation = mAnnotation.getBackpointer();
			return current;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException("remove");
		}
	}
}
