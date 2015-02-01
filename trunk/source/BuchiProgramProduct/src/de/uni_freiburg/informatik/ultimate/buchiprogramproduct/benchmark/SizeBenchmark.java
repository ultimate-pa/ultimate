package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.benchmark;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class SizeBenchmark implements ICsvProviderProvider<Integer> {

	private final int mEdges;
	private final int mLocations;
	private final String mLabel;

	@SuppressWarnings("unused")
	public <E, V> SizeBenchmark(NestedWordAutomaton<E, V> nwa, String label) {
		Collection<V> states = nwa.getStates();
		int edges = 0;
		int locs = 0;
		for (V state : states) {
			++locs;
			for (OutgoingInternalTransition<E, V> out : nwa.internalSuccessors(state)) {
				++edges;
			}
			for (OutgoingCallTransition<E, V> out : nwa.callSuccessors(state)) {
				++edges;
			}
			for (OutgoingReturnTransition<E, V> out : nwa.returnSuccessors(state)) {
				++edges;
			}
			for (SummaryReturnTransition<E, V> out : nwa.returnSummarySuccessor(state)) {
				++edges;
			}
		}
		mEdges = edges;
		mLocations = locs;
		mLabel = label;
	}

	public SizeBenchmark(RootNode root, String label) {
		ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
		HashSet<RCFGEdge> closedE = new HashSet<>();
		HashSet<RCFGNode> closedV = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			RCFGEdge current = edges.removeFirst();
			if (closedE.contains(current)) {
				continue;
			}
			closedE.add(current);
			closedV.add(current.getTarget());
			for (RCFGEdge next : current.getTarget().getOutgoingEdges()) {
				edges.add(next);
			}
		}

		mEdges = closedE.size();
		mLocations = closedV.size();
		mLabel = label;
	}

	@Override
	public ICsvProvider<Integer> createCvsProvider() {
		List<String> columnTitles = new ArrayList<>();
		columnTitles.add(mLabel + " Locations");
		columnTitles.add(mLabel + " Edges");

		List<Integer> row = new ArrayList<>();
		row.add(mLocations);
		row.add(mEdges);

		SimpleCsvProvider<Integer> rtr = new SimpleCsvProvider<>(columnTitles);
		rtr.addRow(row);
		return rtr;
	}

	@Override
	public String toString() {
		return "Locations: " + mLocations + " Edges: " + mEdges;
	}

}
