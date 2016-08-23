/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.benchmark;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
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
	public <E, V> SizeBenchmark(final INestedWordAutomaton<E, V> nwa, final String label) {
		final Collection<V> states = nwa.getStates();
		int edges = 0;
		int locs = 0;
		for (final V state : states) {
			++locs;
			for (final OutgoingInternalTransition<E, V> out : nwa.internalSuccessors(state)) {
				++edges;
			}
			for (final OutgoingCallTransition<E, V> out : nwa.callSuccessors(state)) {
				++edges;
			}
			for (final OutgoingReturnTransition<E, V> out : nwa.returnSuccessors(state)) {
				++edges;
			}
			for (final SummaryReturnTransition<E, V> out : nwa.summarySuccessors(state)) {
				++edges;
			}
		}
		mEdges = edges;
		mLocations = locs;
		mLabel = label;
	}

	public SizeBenchmark(final RootNode root, final String label) {
		final ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
		final HashSet<RCFGEdge> closedE = new HashSet<>();
		final HashSet<RCFGNode> closedV = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			final RCFGEdge current = edges.removeFirst();
			if (closedE.contains(current)) {
				continue;
			}
			closedE.add(current);
			
			if(current.getTarget() == null){
				throw new AssertionError("Target may not be null");
			}
			
			closedV.add(current.getTarget());
			for (final RCFGEdge next : current.getTarget().getOutgoingEdges()) {
				edges.add(next);
			}
		}

		mEdges = closedE.size();
		mLocations = closedV.size();
		mLabel = label;
	}

	@Override
	public ICsvProvider<Integer> createCvsProvider() {
		final List<String> columnTitles = new ArrayList<>();
		columnTitles.add(mLabel + " Locations");
		columnTitles.add(mLabel + " Edges");

		final List<Integer> row = new ArrayList<>();
		row.add(mLocations);
		row.add(mEdges);

		final SimpleCsvProvider<Integer> rtr = new SimpleCsvProvider<>(columnTitles);
		rtr.addRow(row);
		return rtr;
	}

	@Override
	public String toString() {
		return "Locations: " + mLocations + " Edges: " + mEdges;
	}

}
