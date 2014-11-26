package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * Executes a search on an RCFG using an implementation of A*. Finds a path
 * according to a given heuristic from start to target if one exists.
 * 
 * You can specify edges that should be ignored during the search.
 * 
 * @author dietsch
 * 
 */
public class RCFGAStar {

	private final Logger mLogger;
	private final IHeuristic<RCFGNode, RCFGEdge> mHeuristic;
	private final RCFGNode mStart;
	private final RCFGNode mTarget;
	private final HashSet<RCFGEdge> mForbiddenEdges;
	private final HashMap<RCFGNode, AstarAnnotation<RCFGEdge>> mAnnotation;

	public RCFGAStar(Logger logger, RCFGNode start, RCFGNode target, IHeuristic<RCFGNode, RCFGEdge> heuristic) {
		mLogger = logger;
		mStart = start;
		mTarget = target;
		mHeuristic = heuristic;
		mForbiddenEdges = new HashSet<>();
		mAnnotation = new HashMap<>();
	}

	public RCFGAStar(Logger logger, RCFGNode start, RCFGNode target, IHeuristic<RCFGNode, RCFGEdge> heuristic,
			Collection<RCFGEdge> forbiddenEdges) {
		this(logger, start, target, heuristic);
		mForbiddenEdges.addAll(forbiddenEdges);
	}

	public List<RCFGEdge> findPath() {
		// check for trivial paths
		for (RCFGEdge outgoing : mStart.getOutgoingEdges()) {
			if (mForbiddenEdges.contains(outgoing)) {
				continue;
			}
			if (outgoing.getTarget().equals(mTarget)) {
				mLogger.debug("Found trivial path from source " + mStart + " to target " + mTarget + ": " + outgoing);
				return Collections.singletonList(outgoing);
			}
		}

		return astar();
	}

	private List<RCFGEdge> astar() {
		List<RCFGEdge> errorPath = null;

		FasterPriorityQueue<RCFGNode> open = new FasterPriorityQueue<RCFGNode>(new Comparator<RCFGNode>() {
			@Override
			public int compare(RCFGNode o1, RCFGNode o2) {
				return Integer.compare(getAnnotation(o1).getExpectedCostToTarget(), getAnnotation(o2)
						.getExpectedCostToTarget());
			}
		});
		HashSet<RCFGEdge> closed = new HashSet<RCFGEdge>();

		initialize(mStart, open);

		// paths of length 1 are already found in findPath, so we make one run
		// without checking for the target node
		RCFGNode currentNode = open.poll();
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

	private void initialize(RCFGNode node, FasterPriorityQueue<RCFGNode> open) {
		open.add(node);
		AstarAnnotation<RCFGEdge> annot = new AstarAnnotation<RCFGEdge>();
		addAnntotation(node, annot);
	}

	private void expandNode(RCFGNode currentNode, FasterPriorityQueue<RCFGNode> open, HashSet<RCFGEdge> closed) {

		for (RCFGEdge e : currentNode.getOutgoingEdges()) {
			if (mForbiddenEdges.contains(e)) {
				continue;
			}
			RCFGNode successor = e.getTarget();

			AstarAnnotation<RCFGEdge> currentAnnotation = getAnnotation(currentNode);
			AstarAnnotation<RCFGEdge> successorAnnotation = getAnnotation(successor);

			int costSoFar = currentAnnotation.getCostSoFar() + mHeuristic.getConcreteCost(e);

			if (open.contains(successor) && costSoFar >= successorAnnotation.getCostSoFar()) {
				// we already now the successor and our current way is not
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

	private List<RCFGEdge> createErrorPath(RCFGNode target) {
		List<RCFGEdge> rtr = new ArrayList<RCFGEdge>();

		AstarAnnotation<RCFGEdge> currentAnnotation = getAnnotation(target);
		RCFGEdge current = currentAnnotation.getBackPointer();

		// special case: self loop
		if (current.getSource() == current.getTarget() && current.getSource() == mTarget) {
			rtr.add(current);
			return rtr;
		}

		while (current != null) {
			currentAnnotation = getAnnotation(current.getSource());
			rtr.add(current);
			if (current.getSource() == mTarget) {
				break;
			}
			current = currentAnnotation.getBackPointer();
		}

		Collections.reverse(rtr);
		return rtr;
	}

	private void addAnntotation(RCFGNode node, AstarAnnotation<RCFGEdge> annon) {
		mAnnotation.put(node, annon);
	}

	private AstarAnnotation<RCFGEdge> getAnnotation(RCFGNode node) {
		AstarAnnotation<RCFGEdge> annot = mAnnotation.get(node);
		if (annot == null) {
			annot = new AstarAnnotation<RCFGEdge>();
			addAnntotation(node, annot);
		}
		return annot;
	}

	private class AstarAnnotation<E> extends AbstractAnnotations implements Comparable<AstarAnnotation<E>> {

		private static final long serialVersionUID = 1L;
		private E mBackPointer;
		private int mCostSoFar; // g-value
		private int mExpectedCostToTarget; // f-value
		private int mLowestExpectedCost;

		private AstarAnnotation() {
			setExpectedCostToTarget(Integer.MAX_VALUE);
			setLowestExpectedCost(Integer.MAX_VALUE);
		}

		private void setExpectedCostToTarget(int value) {
			mExpectedCostToTarget = value;
			if (value < getLowestExpectedCost()) {
				setLowestExpectedCost(value);
			}
		}

		private boolean isLowest() {
			return getLowestExpectedCost() == getExpectedCostToTarget();
		}

		@Override
		public int compareTo(AstarAnnotation<E> o) {
			return 0;
		}

		@Override
		protected String[] getFieldNames() {
			return new String[] { "mBackPointer", "mCostSoFar", "mExpectedCostToTarget" };
		}

		@Override
		protected Object getFieldValue(String field) {
			try {
				Field f = getClass().getDeclaredField(field);
				f.setAccessible(true);
				return f.get(this);
			} catch (Exception ex) {
				return ex;
			}
		}

		private E getBackPointer() {
			return mBackPointer;
		}

		private void setBackPointer(E backPointer) {
			mBackPointer = backPointer;
		}

		private int getCostSoFar() {
			return mCostSoFar;
		}

		private void setCostSoFar(int costSoFar) {
			mCostSoFar = costSoFar;
		}

		private int getExpectedCostToTarget() {
			return mExpectedCostToTarget;
		}

		private int getLowestExpectedCost() {
			return mLowestExpectedCost;
		}

		private void setLowestExpectedCost(int lowestExpectedCost) {
			mLowestExpectedCost = lowestExpectedCost;
		}
	}

	private class FasterPriorityQueue<E> {
		private PriorityQueue<E> mOpen;
		private HashSet<E> mOpenSupport;

		private FasterPriorityQueue(Comparator<E> comp) {
			mOpen = new PriorityQueue<>(10, comp);
			mOpenSupport = new HashSet<E>();
		}

		public void remove(RCFGNode successor) {
			mOpen.remove(successor);
			mOpenSupport.remove(successor);

		}

		public E poll() {
			E rtr = mOpen.poll();
			mOpenSupport.remove(rtr);
			return rtr;
		}

		public boolean isEmpty() {
			return mOpen.isEmpty();
		}

		public void add(E nodeDecorator) {
			mOpen.add(nodeDecorator);
			mOpenSupport.add(nodeDecorator);
		}

		public boolean contains(E obj) {
			return mOpenSupport.contains(obj);
		}

		@Override
		public String toString() {
			return Utils.join(mOpen, ", ");
		}
	}

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

}
