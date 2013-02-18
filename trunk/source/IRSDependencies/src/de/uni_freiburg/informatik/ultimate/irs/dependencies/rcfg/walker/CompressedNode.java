package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class CompressedNode extends RCFGNode {

	private static final long serialVersionUID = 8389472937782033528L;
	private HashMap<RCFGEdge,List<RCFGEdge>> mShortestPathsToExit;

	private SCC mComponent;

	public CompressedNode(SCC component) {
		if (component == null || component.isEmpty()) {
			throw new IllegalArgumentException();
		} else {

			for (RCFGNode node : component) {
				for (RCFGEdge edge : node.getIncomingEdges()) {
					if (!component.contains(edge.getSource())) {
						mIncomingEdges.add(edge);
					}
				}

				for (RCFGEdge edge : node.getOutgoingEdges()) {
					if (!component.contains(edge.getTarget())) {
						mOutgoingEdges.add(edge);
					}
				}
			}
		}
		mComponent = component;
		mShortestPathsToExit = new HashMap<>();
	}

	public SCC getSCC(){
		return mComponent;
	}
	
	@Override
	public String toString() {
		return mComponent.toString();
	}

	public boolean contains(RCFGNode node) {
		return mComponent.contains(node);
	}
	
	public List<RCFGEdge> getShortestPathToExit(RCFGEdge start){
		if(!mIncomingEdges.contains(start)){
			return null;
		}
		
		if(mShortestPathsToExit.containsKey(start)){
			return mShortestPathsToExit.get(start);
		} else {
			List<RCFGEdge> rtr = shortestPathToExit(start);
			mShortestPathsToExit.put(start, rtr);
			return rtr;
		}
	}
	

	
	protected List<RCFGEdge> shortestPathToExit(RCFGEdge start) {

		LinkedList<EdgeDecorator> queue = new LinkedList<>();
		HashMap<RCFGEdge, EdgeDecorator> set = new HashMap<>();
		LinkedList<EdgeDecorator> exits = new LinkedList<>();

		EdgeDecorator old = getContainer(set, start);
		old.Visits = 1;
		old.pre = null;
		queue.add(old);
		while (!queue.isEmpty()) {
			old = queue.poll();
			EdgeDecorator next;
			for (RCFGEdge edge : old.Node.getOutgoingEdges()) {
				if (edge instanceof Summary) {
					continue;
				}
				next = getContainer(set, edge);
				if (next.Visits == 2) {
					next.Visits = 1;
					next.pre = old;
					if (this.contains(next.Node)) {
						queue.push(next);
					} else {
						exits.add(next);
					}
				}

			}
			old.Visits = 0;
		}

		ArrayList<RCFGEdge> rtrList = new ArrayList<>();
		EdgeDecorator current = exits.get(0);
		while (current != null) {
			rtrList.add(current.Edge);
			current = current.pre;
		}

		return rtrList;

	}
	
	protected EdgeDecorator getContainer(HashMap<RCFGEdge, EdgeDecorator> set,
			RCFGEdge edge){
		return getContainer(set, edge, 2); 
	}
	
	private EdgeDecorator getContainer(HashMap<RCFGEdge, EdgeDecorator> set,
			RCFGEdge edge2, int unrollings) {
		EdgeDecorator container;

		if (set.containsKey(edge2)) {
			container = set.get(edge2);
		} else {
			container = new EdgeDecorator(edge2, unrollings);
			set.put(edge2, container);
		}
		return container;
	}
	
	private class EdgeDecorator implements Comparable<EdgeDecorator> {
		public RCFGNode Node;
		public RCFGEdge Edge;

		public int Visits;

		public EdgeDecorator pre;

		public EdgeDecorator(RCFGEdge edge, int visits) {
			Node = edge.getTarget();
			Edge = edge;
			Visits = visits;
		}

		@Override
		public String toString() {
			return Edge.toString() + "->" + Node.toString() + " ("
					+ String.valueOf(Visits) + ")";
		}

		@Override
		public int compareTo(EdgeDecorator other) {
			if (Visits == other.Visits) {
				return 0;
			} else if (Visits > other.Visits) {
				return 1;
			} else {
				return -1;
			}
		}
		

	}
}
