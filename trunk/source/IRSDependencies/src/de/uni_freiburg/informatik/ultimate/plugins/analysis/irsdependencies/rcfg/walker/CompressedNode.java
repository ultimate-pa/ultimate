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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class CompressedNode extends RCFGNode {

	private static final long serialVersionUID = 8389472937782033528L;
	private final HashMap<RCFGEdge,List<RCFGEdge>> mShortestPathsToExit;

	private final SCC mComponent;

	public CompressedNode(final SCC component) {
		if (component == null || component.isEmpty()) {
			throw new IllegalArgumentException();
		} else {

			for (final RCFGNode node : component) {
				for (final RCFGEdge edge : node.getIncomingEdges()) {
					if (!component.contains(edge.getSource())) {
						mIncomingEdges.add(edge);
					}
				}

				for (final RCFGEdge edge : node.getOutgoingEdges()) {
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

	public boolean contains(final RCFGNode node) {
		return mComponent.contains(node);
	}
	
	public List<RCFGEdge> getShortestPathToExit(final RCFGEdge start){
		if(!mIncomingEdges.contains(start)){
			return null;
		}
		
		if(mShortestPathsToExit.containsKey(start)){
			return mShortestPathsToExit.get(start);
		} else {
			final List<RCFGEdge> rtr = shortestPathToExit(start);
			mShortestPathsToExit.put(start, rtr);
			return rtr;
		}
	}
	

	
	protected List<RCFGEdge> shortestPathToExit(final RCFGEdge start) {

		final LinkedList<EdgeDecorator> queue = new LinkedList<>();
		final HashMap<RCFGEdge, EdgeDecorator> set = new HashMap<>();
		final LinkedList<EdgeDecorator> exits = new LinkedList<>();

		EdgeDecorator old = getContainer(set, start);
		old.Visits = 1;
		old.pre = null;
		queue.add(old);
		while (!queue.isEmpty()) {
			old = queue.poll();
			EdgeDecorator next;
			for (final RCFGEdge edge : old.Node.getOutgoingEdges()) {
				if (edge instanceof Summary) {
					continue;
				}
				next = getContainer(set, edge);
				if (next.Visits == 2) {
					next.Visits = 1;
					next.pre = old;
					if (contains(next.Node)) {
						queue.push(next);
					} else {
						exits.add(next);
					}
				}

			}
			old.Visits = 0;
		}

		final ArrayList<RCFGEdge> rtrList = new ArrayList<>();
		EdgeDecorator current = exits.get(0);
		while (current != null) {
			rtrList.add(current.Edge);
			current = current.pre;
		}

		return rtrList;

	}
	
	protected EdgeDecorator getContainer(final HashMap<RCFGEdge, EdgeDecorator> set,
			final RCFGEdge edge){
		return getContainer(set, edge, 2);
	}
	
	private EdgeDecorator getContainer(final HashMap<RCFGEdge, EdgeDecorator> set,
			final RCFGEdge edge2, final int unrollings) {
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

		public EdgeDecorator(final RCFGEdge edge, final int visits) {
			Node = edge.getTarget();
			Edge = edge;
			Visits = visits;
		}

		@Override
		public String toString() {
			return Edge.toString() + "->" + Node.toString() + " (" + Visits + ')';
		}

		@Override
		public int compareTo(final EdgeDecorator other) {
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
