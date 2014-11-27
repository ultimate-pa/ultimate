package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * Executes a search on an arbitrary graph using an implementation of A*. Finds a path
 * according to a given heuristic from start to target if one exists.
 * 
 * You can specify edges that should be ignored during the search.
 * 
 * @author dietsch
 * 
 */
public class AStar<V, E> {

	private final Logger mLogger; 
	private final IHeuristic<V, E> mHeuristic;
	private final V mStart;
	private final V mTarget;
	private final HashSet<E> mForbiddenEdges;
	private final HashMap<V, AstarAnnotation<E>> mAnnotation;
	private final IGraph<V, E> mGraph;

	public AStar(Logger logger, V start, V target, IHeuristic<V, E> heuristic, IGraph<V, E> graph) {
		mLogger = logger;
		mStart = start;
		mTarget = target;
		mHeuristic = heuristic;
		mForbiddenEdges = new HashSet<>();
		mAnnotation = new HashMap<>();
		mGraph = graph;
	}

	public AStar(Logger logger, V start, V target, IHeuristic<V, E> heuristic, IGraph<V, E> graph,
			Collection<E> forbiddenEdges) {
		this(logger, start, target, heuristic, graph);
		mForbiddenEdges.addAll(forbiddenEdges);
	}

	public List<E> findPath() {
		// check for trivial paths

		for (E outgoing : mGraph.getOutgoingEdges(mStart)) {
			if (mForbiddenEdges.contains(outgoing)) {
				continue;
			}

			if (mGraph.getTarget(outgoing).equals(mTarget)) {
				mLogger.debug("Found trivial path from source " + mStart + " to target " + mTarget + ": " + outgoing);
				return Collections.singletonList(outgoing);
			}
		}

		return astar();
	}

	private List<E> astar() {
		List<E> errorPath = null;

		FasterPriorityQueue<V> open = new FasterPriorityQueue<V>(new Comparator<V>() {
			@Override
			public int compare(V o1, V o2) {
				return Integer.compare(getAnnotation(o1).getExpectedCostToTarget(), getAnnotation(o2)
						.getExpectedCostToTarget());
			}
		});
		HashSet<E> closed = new HashSet<E>();

		initialize(mStart, open);

		// paths of length 1 are already found in findPath, so we make one run
		// without checking for the target node
		V currentNode = open.poll();
		expandNode(currentNode, open, closed);

		while (!open.isEmpty()) {
			currentNode = open.poll();

			if (currentNode.equals(mTarget)) {
				// path found
				errorPath = createErrorPath(currentNode);
				mLogger.debug(String.format("Found path of length %s from source %s to target %s: %s",
						errorPath.size(), mStart, mTarget, Utils.join(errorPath, ", ")));
				break;
			}
			expandNode(currentNode, open, closed);
		}

		return errorPath;
	}

	private void initialize(V node, FasterPriorityQueue<V> open) {
		open.add(node);
		AstarAnnotation<E> annot = new AstarAnnotation<E>();
		addAnntotation(node, annot);
	}

	private void expandNode(V currentNode, FasterPriorityQueue<V> open, HashSet<E> closed) {

		for (E e : mGraph.getOutgoingEdges(currentNode)) {
			if (mForbiddenEdges.contains(e)) {
				continue;
			}

			V successor = mGraph.getTarget(e);

			AstarAnnotation<E> currentAnnotation = getAnnotation(currentNode);
			AstarAnnotation<E> successorAnnotation = getAnnotation(successor);

			int costSoFar = currentAnnotation.getCostSoFar() + mHeuristic.getConcreteCost(e);

			if (open.contains(successor) && costSoFar >= successorAnnotation.getCostSoFar()) {
				// we already know the successor and our current way is not
				// better than the new one
				continue;
			}

			int expectedCost = costSoFar + mHeuristic.getHeuristicValue(successor, mTarget);

			open.remove(successor);
			successorAnnotation.setExpectedCostToTarget(expectedCost);
			if (successorAnnotation.isLowest()) {
				successorAnnotation.setBackPointer(e);
				successorAnnotation.setCostSoFar(costSoFar);
				open.add(successor);
			}
		}

	}

	private List<E> createErrorPath(V target) {
		List<E> rtr = new ArrayList<E>();

		AstarAnnotation<E> currentAnnotation = getAnnotation(target);
		E current = currentAnnotation.getBackPointer();

		// special case: self loop
		if (mGraph.getSource(current) == mGraph.getTarget(current) && mGraph.getSource(current) == mTarget) {
			rtr.add(current);
			return rtr;
		}

		while (current != null) {
			currentAnnotation = getAnnotation(mGraph.getSource(current));
			rtr.add(current);
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

}
