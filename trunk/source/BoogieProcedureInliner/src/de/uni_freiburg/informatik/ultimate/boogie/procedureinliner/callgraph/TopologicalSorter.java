package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.structure.ILabeledEdgesMultigraph;

/**
 * Utility class for topological sorting of DAGs.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <N> Type of the graph's nodes.
 * @param <L> Type of the graph's edge labels.
 */
public class TopologicalSorter<N extends ILabeledEdgesMultigraph<N,L>, L> {
	
	private static class GraphCycleException extends Exception {
		private static final long serialVersionUID = -7189895863479876025L;
	}
	
	ILabeledEdgesFilter<L> mOutgoingEdgesFilter;
	
	Set<N> mUnmarkedNodes;
	Set<N> mTemporarilyMarkedNodes;
	Set<N> mPermanentlyMarkedNodes; 
	List<N> mTopolicalSorting;

	public TopologicalSorter() {
		this(new ILabeledEdgesFilter<L>() {
			@Override
			public boolean accept(L outgoingEdgeLabel) {
				return true;
			}
		});
	}
	
	/**
	 * Creates a sorter, that ignores some of the graphs edges.
	 * This can be used to sort an graph with cycles, if the cycle building edges aren't accepted by the filter.
	 * @param outgoingEdgesFilter Filter to be applied on outgoing edges -- only accepted edges will be used.
	 */
	public TopologicalSorter(ILabeledEdgesFilter<L> outgoingEdgesFilter) {
		mOutgoingEdgesFilter = outgoingEdgesFilter;
	}
	
	/**
	 * Creates a topological order of an acyclic directed graph (DAG).
	 * There are no guarantees, if a node inside <code>graph</code> has a child that isn't part of
	 * <code>graph</code> (except if the edge from the node to it's child isn't accept by the filter).
	 * @param graph All nodes of the graph to be sorted. Duplicates will be ignored.
	 * @return Topological ordering of the graph. null iff the graph contained a circle.
	 */
	public List<N> sortTopological(Collection<N> graph) {
		mUnmarkedNodes = new HashSet<N>(graph);
		mTemporarilyMarkedNodes = new HashSet<N>();
		mPermanentlyMarkedNodes = new HashSet<N>();
		mTopolicalSorting = new ArrayList<N>(graph.size());
		while (!mUnmarkedNodes.isEmpty()) {
			try {
				visit(mUnmarkedNodes.iterator().next());				
			} catch (GraphCycleException gce) {
				return null;
			} 
		}
		Collections.reverse(mTopolicalSorting);
		return mTopolicalSorting;
	}

	// DFS-based algorithm from "http://en.wikipedia.org/wiki/Topological_sorting" (Tarjan, 1976)
	private void visit(N node) throws GraphCycleException {
		if (mTemporarilyMarkedNodes.contains(node)) {
			throw new GraphCycleException();
		} else if (mUnmarkedNodes.contains(node)) {
			markTemporarily(node);
			for (N outgoingNode : node.getOutgoingNodes()) {
				// using "getOutgoingLabel" is not efficient, but the only way without using a less-generic graph type.
				if (mOutgoingEdgesFilter.accept(node.getOutgoingEdgeLabel(outgoingNode))) {
					visit(outgoingNode);
				}
			}
			markPermanently(node);
			mTopolicalSorting.add(node);
		}
	}
	
	private void markTemporarily(N unmarkedNode) {
		mUnmarkedNodes.remove(unmarkedNode);
		mTemporarilyMarkedNodes.add(unmarkedNode);
	}
	
	private void markPermanently(N temporarilyMarkedNode) {
		mTemporarilyMarkedNodes.remove(temporarilyMarkedNode);
		mPermanentlyMarkedNodes.add(temporarilyMarkedNode);
	}
}