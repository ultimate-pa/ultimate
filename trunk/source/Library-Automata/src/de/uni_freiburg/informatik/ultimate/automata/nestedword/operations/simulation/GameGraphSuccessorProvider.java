/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation;

import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;

/**
 * Successor provider for a {@link AGameGraph}. Given a vertex it gets all its
 * successors.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class GameGraphSuccessorProvider<LETTER, STATE> implements ISuccessorProvider<Vertex<LETTER, STATE>> {

	/**
	 * Underlying game graph of the provider.
	 */
	private final AGameGraph<LETTER, STATE> mGraph;

	/**
	 * Creates a new successor provider on a given game graph.
	 * 
	 * @param graph
	 *            The game graph of the provider
	 */
	public GameGraphSuccessorProvider(final AGameGraph<LETTER, STATE> graph) {
		mGraph = graph;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.
	 * ISuccessorProvider#getSuccessors(java.lang.Object)
	 */
	@Override
	public Iterator<Vertex<LETTER, STATE>> getSuccessors(final Vertex<LETTER, STATE> vertex) {
		if (mGraph.hasSuccessors(vertex)) {
			return mGraph.getSuccessors(vertex).iterator();
		} else {
			return new HashSet<Vertex<LETTER, STATE>>().iterator();
		}
	}
}
