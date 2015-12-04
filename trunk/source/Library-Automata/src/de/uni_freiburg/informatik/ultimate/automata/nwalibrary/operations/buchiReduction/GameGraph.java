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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
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
	
	private final HashMap<STATE, HashMap<STATE, HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>>> m_BuechiStatesToGraphDuplicatorVertex;

	private final HashMap<STATE, HashMap<STATE, SpoilerVertex<LETTER, STATE>>> m_BuechiStatesToGraphSpoilerVertex;

	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Predecessors;

	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Successors;

	private final HashSet<SpoilerVertex<LETTER, STATE>> m_SpoilerVertices;

	private final HashSet<DuplicatorVertex<LETTER, STATE>> m_DuplicatorVertices;

	protected final IUltimateServiceProvider m_Services;
	
	public GameGraph(IUltimateServiceProvider services) {
		m_Services = services;
		m_DuplicatorVertices = new HashSet<DuplicatorVertex<LETTER, STATE>>();
		m_SpoilerVertices = new HashSet<SpoilerVertex<LETTER, STATE>>();
		m_Successors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		m_Predecessors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		m_BuechiStatesToGraphSpoilerVertex = new HashMap<STATE, HashMap<STATE, SpoilerVertex<LETTER, STATE>>>();
		m_BuechiStatesToGraphDuplicatorVertex = new HashMap<STATE, HashMap<STATE, HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>>>();
	}

	public Set<DuplicatorVertex<LETTER, STATE>> getDuplicatorVertices() {
		return Collections.unmodifiableSet(m_DuplicatorVertices);
	}

	public Set<SpoilerVertex<LETTER, STATE>> getSpoilerVertices() {
		return Collections.unmodifiableSet(m_SpoilerVertices);
	}

	public Set<Vertex<LETTER, STATE>> getPredecessors(Vertex<LETTER, STATE> vertex) {
		if (hasPredecessors(vertex)) {
			return Collections.unmodifiableSet(m_Predecessors.get(vertex));
		} else {
			return null;
		}
	}

	public Set<Vertex<LETTER, STATE>> getSuccessors(Vertex<LETTER, STATE> vertex) {
		if (hasSuccessors(vertex)) {
			return Collections.unmodifiableSet(m_Successors.get(vertex));
		} else {
			return null;
		}
	}

	public boolean hasPredecessors(Vertex<LETTER, STATE> vertex) {
		return m_Predecessors.containsKey(vertex);
	}

	public boolean hasSuccessors(Vertex<LETTER, STATE> vertex) {
		return m_Successors.containsKey(vertex);
	}
	
	protected DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(STATE q0, STATE q1, LETTER a) {
		HashMap<STATE, HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>> leftMap
			= m_BuechiStatesToGraphDuplicatorVertex.get(q0);
		if (leftMap != null) {
			HashMap<LETTER, DuplicatorVertex<LETTER, STATE>> rightMap
				= leftMap.get(q1);
			if (rightMap != null) {
				return rightMap.get(a);
			}
		}
		return null;
	}
	
	protected SpoilerVertex<LETTER, STATE> getSpoilerVertex(STATE q0, STATE q1) {
		HashMap<STATE, SpoilerVertex<LETTER, STATE>> leftMap
			= m_BuechiStatesToGraphSpoilerVertex.get(q0);
		if (leftMap != null) {
			return leftMap.get(q1);
		}
		return null;
	}

	protected void addEdge(Vertex<LETTER, STATE> src, Vertex<LETTER, STATE> dest) {
		if (!m_Successors.containsKey(src)) {
			m_Successors.put(src, new HashSet<Vertex<LETTER, STATE>>());
		}
		m_Successors.get(src).add(dest);
		if (!m_Predecessors.containsKey(dest)) {
			m_Predecessors.put(dest, new HashSet<Vertex<LETTER, STATE>>());
		}
		m_Predecessors.get(dest).add(src);
	}
	
	protected void addDuplicatorVertex(DuplicatorVertex<LETTER, STATE> vertex) {
		m_DuplicatorVertices.add(vertex);
		STATE q0 = vertex.getQ0();
		HashMap<STATE, HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>> leftMap = m_BuechiStatesToGraphDuplicatorVertex.get(q0);
		if (leftMap == null) {
			m_BuechiStatesToGraphDuplicatorVertex.put(q0, new HashMap<STATE, HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>>());
		}
		STATE q1 = vertex.getQ1();
		HashMap<LETTER, DuplicatorVertex<LETTER, STATE>> rightMap = m_BuechiStatesToGraphDuplicatorVertex.get(q0).get(q1);
		if (rightMap == null) {
			m_BuechiStatesToGraphDuplicatorVertex.get(q0).put(q1, new HashMap<LETTER, DuplicatorVertex<LETTER, STATE>>());
		}
		m_BuechiStatesToGraphDuplicatorVertex.get(q0).get(q1).put(vertex.getLetter(), vertex);
	}
	
	protected void addSpoilerVertex(SpoilerVertex<LETTER, STATE> vertex) {
		m_SpoilerVertices.add(vertex);
		STATE q0 = vertex.getQ0();
		HashMap<STATE, SpoilerVertex<LETTER, STATE>> leftMap = m_BuechiStatesToGraphSpoilerVertex.get(q0);
		if (leftMap == null) {
			m_BuechiStatesToGraphSpoilerVertex.put(q0, new HashMap<STATE, SpoilerVertex<LETTER, STATE>>());
		}
		m_BuechiStatesToGraphSpoilerVertex.get(q0).put(vertex.getQ1(), vertex);
	}

	protected abstract int calculatePriority(STATE leftState, STATE rightState);

	protected abstract void generateGameGraphFromBuechi();

	protected abstract NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph();
	
	public int getSize() {
		return m_SpoilerVertices.size() + m_DuplicatorVertices.size();
	}
	
	public Set<Vertex<LETTER, STATE>> getVertices() {
		HashSet<Vertex<LETTER, STATE>> result = new HashSet<Vertex<LETTER, STATE>>(m_SpoilerVertices);
		result.addAll(m_DuplicatorVertices);
		return result;
	}
	
	public Set<Vertex<LETTER, STATE>> getNonDeadEndVertices() {
		return Collections.unmodifiableSet(m_Successors.keySet());
	}
}
