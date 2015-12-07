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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class AGameGraph<LETTER, STATE> {
	
	private final NestedMap4<STATE, STATE, LETTER, Boolean,
		DuplicatorVertex<LETTER, STATE>> m_BuechiStatesToGraphDuplicatorVertex;

	private final NestedMap3<STATE, STATE, Boolean,
		SpoilerVertex<LETTER, STATE>> m_BuechiStatesToGraphSpoilerVertex;

	private final HashSet<DuplicatorVertex<LETTER, STATE>> m_DuplicatorVertices;

	private int m_GlobalInfinity;

	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Predecessors;

	private final IUltimateServiceProvider m_Services;
	
	private final HashSet<SpoilerVertex<LETTER, STATE>> m_SpoilerVertices;

	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Successors;
	
	public AGameGraph(final IUltimateServiceProvider services) {
		m_Services = services;
		m_DuplicatorVertices = new HashSet<DuplicatorVertex<LETTER, STATE>>();
		m_SpoilerVertices = new HashSet<SpoilerVertex<LETTER, STATE>>();
		m_Successors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		m_Predecessors = new HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>>();
		m_BuechiStatesToGraphSpoilerVertex = new NestedMap3<STATE, STATE, Boolean,
				SpoilerVertex<LETTER, STATE>>();
		m_BuechiStatesToGraphDuplicatorVertex = new NestedMap4<STATE, STATE, LETTER, Boolean,
				DuplicatorVertex<LETTER, STATE>>();
		m_GlobalInfinity = 0;
	}
	
	public void clear() {
		m_BuechiStatesToGraphDuplicatorVertex.clear();
		m_BuechiStatesToGraphSpoilerVertex.clear();
		m_Predecessors.clear();
		m_Successors.clear();
		m_SpoilerVertices.clear();
		m_DuplicatorVertices.clear();
	}
	
	// TODO Change visibility down to protected
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0,
			final STATE q1, final LETTER a, final boolean bit) {
		return m_BuechiStatesToGraphDuplicatorVertex.get(q0, q1, a, bit);
	}
	
	public Set<DuplicatorVertex<LETTER, STATE>> getDuplicatorVertices() {
		return Collections.unmodifiableSet(m_DuplicatorVertices);
	}

	public int getGlobalInfinity() {
		return m_GlobalInfinity;
	}

	public Set<Vertex<LETTER, STATE>> getNonDeadEndVertices() {
		return Collections.unmodifiableSet(m_Successors.keySet());
	}

	public Set<Vertex<LETTER, STATE>> getPredecessors(final Vertex<LETTER, STATE> vertex) {
		if (hasPredecessors(vertex)) {
			return Collections.unmodifiableSet(m_Predecessors.get(vertex));
		} else {
			return null;
		}
	}

	public int getSize() {
		return m_SpoilerVertices.size() + m_DuplicatorVertices.size();
	}

	// TODO Change visibility down to protected
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0,
			final STATE q1, final boolean bit) {
		return m_BuechiStatesToGraphSpoilerVertex.get(q0, q1, bit);
	}

	public Set<SpoilerVertex<LETTER, STATE>> getSpoilerVertices() {
		return Collections.unmodifiableSet(m_SpoilerVertices);
	}
	
	public Collection<Set<Vertex<LETTER,STATE>>> getSuccessorGroups() {
		return Collections.unmodifiableCollection(m_Successors.values());
	}
	
	public Set<Vertex<LETTER, STATE>> getSuccessors(final Vertex<LETTER, STATE> vertex) {
		if (hasSuccessors(vertex)) {
			return Collections.unmodifiableSet(m_Successors.get(vertex));
		} else {
			return null;
		}
	}

	public Set<Vertex<LETTER, STATE>> getVertices() {
		HashSet<Vertex<LETTER, STATE>> result = new HashSet<Vertex<LETTER, STATE>>(m_SpoilerVertices);
		result.addAll(m_DuplicatorVertices);
		return result;
	}
	
	public boolean hasPredecessors(final Vertex<LETTER, STATE> vertex) {
		return m_Predecessors.containsKey(vertex);
	}
	
	public boolean hasSuccessors(final Vertex<LETTER, STATE> vertex) {
		return m_Successors.containsKey(vertex);
	}

	protected void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		m_DuplicatorVertices.add(vertex);
		m_BuechiStatesToGraphDuplicatorVertex.put(vertex.getQ0(), vertex.getQ1(),
				vertex.getLetter(), vertex.isB(), vertex);
	}

	protected void addEdge(final Vertex<LETTER, STATE> src,
			final Vertex<LETTER, STATE> dest) {
		if (!m_Successors.containsKey(src)) {
			m_Successors.put(src, new HashSet<Vertex<LETTER, STATE>>());
		}
		m_Successors.get(src).add(dest);
		if (!m_Predecessors.containsKey(dest)) {
			m_Predecessors.put(dest, new HashSet<Vertex<LETTER, STATE>>());
		}
		m_Predecessors.get(dest).add(src);
	}
	
	protected void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		m_SpoilerVertices.add(vertex);
		m_BuechiStatesToGraphSpoilerVertex.put(vertex.getQ0(), vertex.getQ1(),
				vertex.isB(), vertex);
	}
	
	protected abstract NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph()
			throws OperationCanceledException ;
	
	protected abstract void generateGameGraphFromBuechi() throws OperationCanceledException ;
	
	protected IUltimateServiceProvider getServiceProvider() {
		return m_Services;
	}
	
	protected void increaseGlobalInfinity() {
		m_GlobalInfinity++;
	}

	protected void setGlobalInfinity(final int globalInfinity) {
		m_GlobalInfinity = globalInfinity;
	}
}
