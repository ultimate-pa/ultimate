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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class GameGraph<LETTER, STATE> {
	
	private HashMap<STATE, HashMap<STATE, HashMap<LETTER, Player0Vertex<LETTER, STATE>>>> buechiStatesToGraphStateV0;

	private HashMap<STATE, HashMap<STATE, Player1Vertex<LETTER, STATE>>> buechiStatesToGraphStateV1;

	private HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> predecessors;

	private HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> successors;

	private HashSet<Player1Vertex<LETTER, STATE>> vOneStates;

	private HashSet<Player0Vertex<LETTER, STATE>> vZeroStates;

	protected final IUltimateServiceProvider m_Services;
	
	public GameGraph(IUltimateServiceProvider services) {
		m_Services = services;
		vZeroStates = new HashSet<Player0Vertex<LETTER, STATE>>();
		vOneStates = new HashSet<Player1Vertex<LETTER, STATE>>();
		successors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		predecessors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		buechiStatesToGraphStateV1 = new HashMap<STATE, HashMap<STATE, Player1Vertex<LETTER, STATE>>>();
		buechiStatesToGraphStateV0 = new HashMap<STATE, HashMap<STATE, HashMap<LETTER, Player0Vertex<LETTER, STATE>>>>();
	}

	public Set<Player0Vertex<LETTER, STATE>> getPlayer0States() {
		return Collections.unmodifiableSet(vZeroStates);
	}

	public Set<Player1Vertex<LETTER, STATE>> getPlayer1States() {
		return Collections.unmodifiableSet(vOneStates);
	}

	public Set<Vertex<LETTER, STATE>> getPredecessors(Vertex<LETTER, STATE> v) {
		if (hasPredecessors(v)) {
			return Collections.unmodifiableSet(predecessors.get(v));
		} else {
			return null;
		}
	}

	public Set<Vertex<LETTER, STATE>> getSuccessors(Vertex<LETTER, STATE> v) {
		if (hasSuccessors(v)) {
			return Collections.unmodifiableSet(successors.get(v));
		} else {
			return null;
		}
	}

	public boolean hasPredecessors(Vertex<LETTER, STATE> v) {
		return predecessors.containsKey(v);
	}

	public boolean hasSuccessors(Vertex<LETTER, STATE> v) {
		return successors.containsKey(v);
	}
	
	protected Player0Vertex<LETTER, STATE> getPlayer0State(STATE q0, STATE q1, LETTER a) {
		HashMap<STATE, HashMap<LETTER, Player0Vertex<LETTER, STATE>>> leftMap
			= buechiStatesToGraphStateV0.get(q0);
		if (leftMap != null) {
			HashMap<LETTER, Player0Vertex<LETTER, STATE>> rightMap
				= leftMap.get(q1);
			if (rightMap != null) {
				return rightMap.get(a);
			}
		}
		return null;
	}
	
	protected Player1Vertex<LETTER, STATE> getPlayer1State(STATE q0, STATE q1) {
		HashMap<STATE, Player1Vertex<LETTER, STATE>> leftMap
			= buechiStatesToGraphStateV1.get(q0);
		if (leftMap != null) {
			return leftMap.get(q1);
		}
		return null;
	}

	protected void addEdge(Vertex<LETTER, STATE> src, Vertex<LETTER, STATE> dest) {
		if (!successors.containsKey(src)) {
			successors.put(src, new HashSet<Vertex<LETTER, STATE>>());
		}
		successors.get(src).add(dest);
		if (!predecessors.containsKey(dest)) {
			predecessors.put(dest, new HashSet<Vertex<LETTER, STATE>>());
		}
		predecessors.get(dest).add(src);
	}
	
	protected void addPlayer0State(Player0Vertex<LETTER, STATE> state) {
		vZeroStates.add(state);
		STATE q0 = state.getQ0();
		HashMap<STATE, HashMap<LETTER, Player0Vertex<LETTER, STATE>>> leftMap = buechiStatesToGraphStateV0.get(q0);
		if (leftMap == null) {
			buechiStatesToGraphStateV0.put(q0, new HashMap<STATE, HashMap<LETTER, Player0Vertex<LETTER, STATE>>>());
		}
		STATE q1 = state.getQ1();
		HashMap<LETTER, Player0Vertex<LETTER, STATE>> rightMap = buechiStatesToGraphStateV0.get(q0).get(q1);
		if (rightMap == null) {
			buechiStatesToGraphStateV0.get(q0).put(q1, new HashMap<LETTER, Player0Vertex<LETTER, STATE>>());
		}
		buechiStatesToGraphStateV0.get(q0).get(q1).put(state.getLetter(), state);
	}
	
	protected void addPlayer1State(Player1Vertex<LETTER, STATE> state) {
		vOneStates.add(state);
		STATE q0 = state.getQ0();
		HashMap<STATE, Player1Vertex<LETTER, STATE>> leftMap = buechiStatesToGraphStateV1.get(q0);
		if (leftMap == null) {
			buechiStatesToGraphStateV1.put(q0, new HashMap<STATE, Player1Vertex<LETTER, STATE>>());
		}
		buechiStatesToGraphStateV1.get(q0).put(state.getQ1(), state);
	}

	protected abstract byte calculatePriority(STATE leftState, STATE rightState);

	protected abstract void generateGameGraphFromBuechi();

	protected abstract NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph();
	
	public int getSize() {
		return vOneStates.size() + vZeroStates.size();
	}
	
	public Set<Vertex<LETTER, STATE>> getStates() {
		HashSet<Vertex<LETTER, STATE>> result = new HashSet<Vertex<LETTER, STATE>>(vOneStates);
		result.addAll(vZeroStates);
		return result;
	}
	
	public Set<Vertex<LETTER, STATE>> getNonDeadEndStates() {
		return Collections.unmodifiableSet(successors.keySet());
	}
}
