package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.util.Utils;

public class RCFGWalkerAStar extends RCFGWalker {

	private FasterPriorityQueue<RCFGNode> mOpen;
	private HashSet<RCFGNode> mClosed;
	private HashMap<String, HashMap<ProgramPoint, List<RCFGEdge>>> mErrorPaths;

	public RCFGWalkerAStar(ObserverDispatcher dispatcher, Logger logger) {
		super(dispatcher, logger);
		mOpen = new FasterPriorityQueue<RCFGNode>(new Comparator<RCFGNode>() {
			@Override
			public int compare(RCFGNode o1, RCFGNode o2) {
				return Integer
						.compare(getAnnotation(o1).mExpectedCostToTarget, getAnnotation(o2).mExpectedCostToTarget);
			}
		});
		mErrorPaths = new HashMap<String, HashMap<ProgramPoint, List<RCFGEdge>>>();
		mClosed = new HashSet<RCFGNode>();
	}

	@Override
	public void processProgram(RootNode node) {
		mLogger.debug("Starting...");

		Map<String, Collection<ProgramPoint>> errorLocs = node.getRootAnnot().getErrorNodes();
		for (String s : errorLocs.keySet()) {
			for (ProgramPoint target : errorLocs.get(s)) {

				addAnntotation(node, new AstarAnnotation());

				mOpen.add(node);

				while (!mOpen.isEmpty()) {
					RCFGNode currentNode = mOpen.poll();
					
					if (currentNode.equals(target)) {
						// path found

						List<RCFGEdge> errorPath = createErrorPath(currentNode);
						addErrorPath(errorPath, target, s);
						mLogger.debug(String.format("Path of length %s found", errorPath.size()));
						mLogger.debug(Utils.join(errorPath, ", "));
						mOpen.Clear();
						mClosed.clear();					
						
					} else {
						mClosed.add(currentNode);
						expandNode(currentNode);
					}
				}
			}
		}
	}

	private void expandNode(RCFGNode currentNode) {
		for (RCFGEdge e : currentNode.getOutgoingEdges()) {
			RCFGNode successor = e.getTarget();
			
			if (mClosed.contains(successor)) {
				continue;
			}

			AstarAnnotation currentAnnotation = getAnnotation(currentNode);
			AstarAnnotation successorAnnotation = getAnnotation(successor);

			int estimatedCost = currentAnnotation.mCostSoFar + getConcreteCost(e);

			if (mOpen.contains(successor) && estimatedCost >= successorAnnotation.mCostSoFar) {
				// we already now the successor and our current way is not
				// better than the new one
				continue;
			}

			successorAnnotation.mBackPointer = e;
			successorAnnotation.mCostSoFar = estimatedCost;

			int expectedCost = estimatedCost + getHeuristicValue(successor);

			mOpen.remove(successor);
			getAnnotation(successor).mExpectedCostToTarget = expectedCost;
			mOpen.add(successor);
		}

	}

	private int getHeuristicValue(RCFGNode successor) {
		return 0;
	}

	private int getConcreteCost(RCFGEdge e) {
		return 1;
	}

	private List<RCFGEdge> createErrorPath(RCFGNode target) {
		List<RCFGEdge> rtr = new ArrayList<RCFGEdge>();
		
		RCFGEdge current = getAnnotation(target).mBackPointer;
		AstarAnnotation currentAnnotation; 

		while (current != null) {
			currentAnnotation = getAnnotation(current.getSource());
			rtr.add(current);
			current = currentAnnotation.mBackPointer;
		}

		Collections.reverse(rtr);
		return rtr;
	}

	private void addErrorPath(List<RCFGEdge> path, ProgramPoint errorLoc, String methodName) {
		HashMap<ProgramPoint, List<RCFGEdge>> methodMap = mErrorPaths.get(methodName);
		if (methodMap == null) {
			methodMap = new HashMap<ProgramPoint, List<RCFGEdge>>();
			mErrorPaths.put(methodName, methodMap);
		}
		methodMap.put(errorLoc, path);
	}

	private void addAnntotation(RCFGNode node, AstarAnnotation annon) {
		node.getPayload().getAnnotations().put("Astar", annon);
	}

	private AstarAnnotation getAnnotation(RCFGNode node) {
		IAnnotations rtr = node.getPayload().getAnnotations().get("Astar");
		if (rtr == null) {
			rtr = new AstarAnnotation();
			addAnntotation(node, (AstarAnnotation) rtr);
		}
		return (AstarAnnotation) rtr;
	}

	private class AstarAnnotation extends AbstractAnnotations implements Comparable<AstarAnnotation> {

		private static final long serialVersionUID = 1L;
		private RCFGEdge mBackPointer;
		private int mCostSoFar; // g-value
		private int mExpectedCostToTarget; // f-value

		private AstarAnnotation() {
		}

		@Override
		public int compareTo(AstarAnnotation o) {
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
	}

	private class FasterPriorityQueue<E> {
		private PriorityQueue<E> mOpen;
		private HashSet<E> mOpenSupport;

		private FasterPriorityQueue(Comparator<E> comp) {
			mOpen = new PriorityQueue<>(10, comp);
			mOpenSupport = new HashSet<E>();
		}

		public void Clear() {
			mOpen.clear();
			mOpenSupport.clear();

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
	}

}
