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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.VertexValueContainer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Abstract class for game graphs which are needed for simulation calculation.
 * <br/>
 * <br/>
 * 
 * A game graph represents a game played by <i>Spoiler</i> and <i>Duplicator</i>
 * on an original buechi automaton.<br/>
 * <i>Spoiler</i> tries to build an accepting word <i>Duplicator</i> can not
 * reproduce. If <i>Spoiler</i> fails we say <b>q1 simulates q0</b> if
 * <i>Spoilers</i> starting state was q0 and <i>Duplicators</i> q1.<br/>
 * <br/>
 * 
 * The exact winning conditions are determined by special instances of graphs
 * which should extend this class.<br/>
 * Given such an instance a game graph needs to generate itself out of a buechi
 * automaton and be able to generate a reduced buechi automaton as a result of a
 * so called simulation.<br/>
 * This game graph class is also capable of undoing made changes by using the
 * {@link #undoChanges(GameGraphChanges) undoChanges} method and maintaining a
 * {@link GameGraphChanges} object.<br/>
 * <br/>
 * 
 * For simulations see {@link ASimulation}.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public abstract class AGameGraph<LETTER, STATE> {
	/**
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(State of spoiler or q0, Letter spoiler used before, State of
	 * duplicator or q1, bit)</b>.
	 */
	private final NestedMap4<STATE, STATE, LETTER, Boolean, DuplicatorVertex<LETTER, STATE>> m_BuechiStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects
	 * by using their representation:<br/>
	 * <b>(State of spoiler or q0, State of duplicator or q1, bit)</b>.
	 */
	private final NestedMap3<STATE, STATE, Boolean, SpoilerVertex<LETTER, STATE>> m_BuechiStatesToGraphSpoilerVertex;
	/**
	 * Set of all {@link DuplicatorVertex} objects the game graph holds.
	 */
	private final HashSet<DuplicatorVertex<LETTER, STATE>> m_DuplicatorVertices;
	/**
	 * The upper bound which, as counter interpreted, represents at which point
	 * one can be sure that vertices with priority 1 can be visited infinite
	 * times without visiting priority 0.<br/>
	 * In general this is the <b>number of vertices with priority 1 plus 1</b>.
	 */
	private int m_GlobalInfinity;
	/**
	 * Data structure that allows a fast access to predecessors of a given
	 * vertex in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Predecessors;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final IUltimateServiceProvider m_Services;
	/**
	 * Set of all {@link SpoilerVertex} objects the game graph holds.
	 */
	private final HashSet<SpoilerVertex<LETTER, STATE>> m_SpoilerVertices;
	/**
	 * State factory used for state creation.
	 */
	private final StateFactory<STATE> m_StateFactory;
	/**
	 * Data structure that allows a fast access to successors of a given vertex
	 * in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> m_Successors;

	/**
	 * Creates a new game graph object that initializes all needed data
	 * structures.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            State factory used for state creation
	 */
	public AGameGraph(final IUltimateServiceProvider services, final StateFactory<STATE> stateFactory) {
		m_Services = services;
		m_StateFactory = stateFactory;
		m_DuplicatorVertices = new HashSet<>();
		m_SpoilerVertices = new HashSet<>();
		m_Successors = new HashMap<>();
		m_Predecessors = new HashMap<>();
		m_BuechiStatesToGraphSpoilerVertex = new NestedMap3<>();
		m_BuechiStatesToGraphDuplicatorVertex = new NestedMap4<>();
		m_GlobalInfinity = 0;
	}

	/**
	 * Gets the {@link DuplicatorVertex} object of the game graph by its
	 * representation or <tt>null</tt> if there is no such.
	 * 
	 * @param q0
	 *            The state spoiler is currently at
	 * @param q1
	 *            The state duplicator is currently at
	 * @param a
	 *            The letter spoiler used before
	 * @param bit
	 *            The bit of the vertex
	 * @return The {@link DuplicatorVertex} object represented by arguments or
	 *         <tt>null</tt> if there is no such.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit) {
		return m_BuechiStatesToGraphDuplicatorVertex.get(q0, q1, a, bit);
	}

	/**
	 * Gets an unmodifiable set of all {@link DuplicatorVertex} objects the game
	 * graph has.
	 * 
	 * @return An unmodifiable set of all {@link DuplicatorVertex} objects the
	 *         game graph has.
	 */
	public Set<DuplicatorVertex<LETTER, STATE>> getDuplicatorVertices() {
		return Collections.unmodifiableSet(m_DuplicatorVertices);
	}

	/**
	 * Gets the global infinity.<br/>
	 * The upper bound which, as counter interpreted, represents at which point
	 * one can be sure that vertices with priority 1 can be visited infinite
	 * times without visiting priority 0.<br/>
	 * In general this is the <b>number of vertices with priority 1 plus 1</b>.
	 * 
	 * @return The global infinity
	 */
	public int getGlobalInfinity() {
		return m_GlobalInfinity;
	}

	/**
	 * Gets an unmodifiable set of all {@link Vertex} objects the game graph has
	 * that do have successors, also known as non dead end.
	 * 
	 * @return An unmodifiable set of all {@link Vertex} objects the game graph
	 *         has that do have successors.
	 */
	public Set<Vertex<LETTER, STATE>> getNonDeadEndVertices() {
		return Collections.unmodifiableSet(m_Successors.keySet());
	}

	/**
	 * Gets an unmodifiable set of all predecessors a given {@link Vertex} has
	 * or <tt>null</tt> if it has no.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return An unmodifiable set of all predecessors the given {@link Vertex}
	 *         has or <tt>null</tt> if it has no.
	 */
	public Set<Vertex<LETTER, STATE>> getPredecessors(final Vertex<LETTER, STATE> vertex) {
		if (hasPredecessors(vertex)) {
			return Collections.unmodifiableSet(m_Predecessors.get(vertex));
		} else {
			return null;
		}
	}

	/**
	 * Gets the priority of a given vertex.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return The priority of the given vertex
	 * @throws IllegalArgumentException
	 *             If the given vertex is <tt>null</tt>.
	 */
	public int getPriority(Vertex<LETTER, STATE> vertex) {
		if (vertex == null) {
			throw new IllegalArgumentException("The given vertex must not be null.");
		}
		return vertex.getPriority();
	}

	/**
	 * Gets the size of the game graph which is the number of all vertices.
	 * 
	 * @return The size of the game graph which is the number of all vertices.
	 */
	public int getSize() {
		return m_SpoilerVertices.size() + m_DuplicatorVertices.size();
	}

	/**
	 * Gets the {@link SpoilerVertex} object of the game graph by its
	 * representation or <tt>null</tt> if there is no such.
	 * 
	 * @param q0
	 *            The state spoiler is currently at
	 * @param q1
	 *            The state duplicator is currently at
	 * @param bit
	 *            The bit of the vertex
	 * @return The {@link SpoilerVertex} object represented by arguments or
	 *         <tt>null</tt> if there is no such.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit) {
		return m_BuechiStatesToGraphSpoilerVertex.get(q0, q1, bit);
	}

	/**
	 * Gets an unmodifiable set of all {@link SpoilerVertex} objects the game
	 * graph has.
	 * 
	 * @return An unmodifiable set of all {@link SpoilerVertex} objects the game
	 *         graph has.
	 */
	public Set<SpoilerVertex<LETTER, STATE>> getSpoilerVertices() {
		return Collections.unmodifiableSet(m_SpoilerVertices);
	}

	/**
	 * Gets an unmodifiable collection of all successor vertices grouped by
	 * their predecessors.
	 * 
	 * @return An unmodifiable collection of all successor vertices grouped by
	 *         their predecessors.
	 */
	public Collection<Set<Vertex<LETTER, STATE>>> getSuccessorGroups() {
		return Collections.unmodifiableCollection(m_Successors.values());
	}

	/**
	 * Gets an unmodifiable set of all successors a given {@link Vertex} has or
	 * <tt>null</tt> if it has no.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return An unmodifiable set of all successors the given {@link Vertex}
	 *         has or <tt>null</tt> if it has no.
	 */
	public Set<Vertex<LETTER, STATE>> getSuccessors(final Vertex<LETTER, STATE> vertex) {
		if (hasSuccessors(vertex)) {
			return Collections.unmodifiableSet(m_Successors.get(vertex));
		} else {
			return null;
		}
	}

	/**
	 * Gets all {@link Vertex} objects the game graph has.
	 * 
	 * @return All {@link Vertex} objects the game graph has.
	 */
	public Set<Vertex<LETTER, STATE>> getVertices() {
		HashSet<Vertex<LETTER, STATE>> result = new HashSet<>(m_SpoilerVertices);
		result.addAll(m_DuplicatorVertices);
		return result;
	}

	/**
	 * If a given {@link Vertex} has predecessor vertices or not.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the vertex has predecessors, false if not.
	 */
	public boolean hasPredecessors(final Vertex<LETTER, STATE> vertex) {
		return m_Predecessors.containsKey(vertex);
	}

	/**
	 * If a given {@link Vertex} has successor vertices or not.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the vertex has successors, false if not.
	 */
	public boolean hasSuccessors(final Vertex<LETTER, STATE> vertex) {
		return m_Successors.containsKey(vertex);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("GameGraph gg = (");

		// Vertices
		result.append(lineSeparator + "\tSpoilerVertices = {");
		for (SpoilerVertex<LETTER, STATE> vertex : getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), p:"
					+ getPriority(vertex) + ">");
		}
		result.append(lineSeparator + "\t},");
		result.append(lineSeparator + "\tDuplicatorVertices = {");
		for (DuplicatorVertex<LETTER, STATE> vertex : getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), p:" + getPriority(vertex) + ">");
		}
		result.append(lineSeparator + "\t},");

		// Edges
		result.append(lineSeparator + "\tedges = {");
		for (Vertex<LETTER, STATE> vertex : getNonDeadEndVertices()) {
			for (Vertex<LETTER, STATE> succ : getSuccessors(vertex)) {
				result.append(lineSeparator + "\t\t(" + vertex.getQ0() + ", " + vertex.getQ1());
				if (vertex instanceof DuplicatorVertex) {
					DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertex;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")\t--> (" + succ.getQ0() + ", " + succ.getQ1());
				if (succ instanceof DuplicatorVertex) {
					DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) succ;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")");
			}
		}
		result.append(lineSeparator + "\t}");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Undoes to the graph made changes represented by a given
	 * {@link GameGraphChanges} object.
	 * 
	 * @param changes
	 *            The changes to undo
	 */
	public void undoChanges(final GameGraphChanges<LETTER, STATE> changes) {
		if (changes == null) {
			return;
		}

		// Undo edge changes
		NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, GameGraphChangeType> changedEdges = changes
				.getChangedEdges();
		for (Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, GameGraphChangeType> changedEdge : changedEdges
				.entrySet()) {
			Vertex<LETTER, STATE> src = changedEdge.getFirst();
			Vertex<LETTER, STATE> dest = changedEdge.getSecond();
			GameGraphChangeType type = changedEdge.getThird();
			// If added before, remove and vice versa
			if (type.equals(GameGraphChangeType.ADDITION)) {
				removeEdge(src, dest);
			} else if (type.equals(GameGraphChangeType.REMOVAL)) {
				addEdge(src, dest);
			}
		}

		// Undo vertex changes
		HashMap<Vertex<LETTER, STATE>, GameGraphChangeType> changedVertices = changes.getChangedVertices();
		for (Entry<Vertex<LETTER, STATE>, GameGraphChangeType> changedVertex : changedVertices.entrySet()) {
			Vertex<LETTER, STATE> vertex = changedVertex.getKey();
			GameGraphChangeType type = changedVertex.getValue();
			// If added before, remove and vice versa
			if (type.equals(GameGraphChangeType.ADDITION)) {
				if (vertex.isDuplicatorVertex()) {
					removeDuplicatorVertex((DuplicatorVertex<LETTER, STATE>) vertex);
				} else if (vertex.isSpoilerVertex()) {
					removeSpoilerVertex((SpoilerVertex<LETTER, STATE>) vertex);
				}
			} else if (type.equals(GameGraphChangeType.REMOVAL)) {
				if (vertex.isDuplicatorVertex()) {
					addDuplicatorVertex((DuplicatorVertex<LETTER, STATE>) vertex);
				} else if (vertex.isSpoilerVertex()) {
					addSpoilerVertex((SpoilerVertex<LETTER, STATE>) vertex);
				}
			}
		}

		// Undo vertex value changes
		HashMap<Vertex<LETTER, STATE>, VertexValueContainer> changedVertexValues = changes.getRememberedVertexValues();
		for (Entry<Vertex<LETTER, STATE>, VertexValueContainer> changedValues : changedVertexValues.entrySet()) {
			Vertex<LETTER, STATE> vertex = changedValues.getKey();
			VertexValueContainer values = changedValues.getValue();
			// Only undo if there actually is a changed value stored
			// Undo PM
			if (VertexValueContainer.isValueValid(values.getProgressMeasure())) {
				vertex.setPM(values.getProgressMeasure());
			}
			// Undo BEff
			if (VertexValueContainer.isValueValid(values.getBestNeighborMeasure())) {
				vertex.setBEff(values.getBestNeighborMeasure());
			}
			// Undo C
			if (VertexValueContainer.isValueValid(values.getNeighborCounter())) {
				vertex.setC(values.getNeighborCounter());
			}
		}
	}

	/**
	 * Adds a given {@link DuplicatorVertex} object to the game graph.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		m_DuplicatorVertices.add(vertex);
		m_BuechiStatesToGraphDuplicatorVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.getLetter(), vertex.isB(),
				vertex);
	}

	/**
	 * Adds a given edge, represented by its source and destination, to the game
	 * graph.
	 * 
	 * @param src
	 *            Source of the edge
	 * @param dest
	 *            Destination of the edge
	 */
	protected void addEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (!m_Successors.containsKey(src)) {
			m_Successors.put(src, new HashSet<>());
		}
		m_Successors.get(src).add(dest);

		// Update predecessor information
		if (!m_Predecessors.containsKey(dest)) {
			m_Predecessors.put(dest, new HashSet<>());
		}
		m_Predecessors.get(dest).add(src);
	}

	/**
	 * Adds a given {@link SpoilerVertex} object to the game graph.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		m_SpoilerVertices.add(vertex);
		m_BuechiStatesToGraphSpoilerVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.isB(), vertex);
	}

	/**
	 * Generates a possible reduced buechi automaton by using the current state
	 * of the game graph that may hold information, usable for reduction,
	 * generated by an {@link ASimulation}.
	 * 
	 * @return A possible reduced buechi automaton
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected abstract INestedWordAutomatonOldApi<LETTER, STATE> generateBuchiAutomatonFromGraph()
			throws OperationCanceledException;

	/**
	 * Generates the game graph out of an original buechi automaton. The graph
	 * represents a game, see {@link AGameGraph}.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected abstract void generateGameGraphFromBuechi() throws OperationCanceledException;

	/**
	 * Gets the used service provider of the Ultimate framework.
	 * 
	 * @return The used service provider of the Ultimate framework.
	 */
	protected IUltimateServiceProvider getServiceProvider() {
		return m_Services;
	}

	/**
	 * Gets the state factory used for state creation.
	 * 
	 * @return The state factory used for state creation
	 */
	protected StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

	/**
	 * Increases the current global infinity bound by one.<br/>
	 * For more information see {@link #getGlobalInfinity()}.
	 */
	protected void increaseGlobalInfinity() {
		m_GlobalInfinity++;
	}

	/**
	 * Removes a given {@link DuplicatorVertex} object from the game graph.
	 * 
	 * @param vertex
	 *            The vertex to remove
	 */
	protected void removeDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		m_DuplicatorVertices.remove(vertex);
		m_BuechiStatesToGraphDuplicatorVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.getLetter(), vertex.isB(),
				null);
	}

	/**
	 * Removes a given edge, represented by its source and destination, from the
	 * game graph.
	 * 
	 * @param src
	 *            Source of the edge
	 * @param dest
	 *            Destination of the edge
	 */
	protected void removeEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (m_Successors.get(src) != null) {
			m_Successors.get(src).remove(dest);
			if (m_Successors.get(src).size() == 0) {
				m_Successors.remove(src);
			}
		}

		// Update predecessor information
		if (m_Predecessors.get(dest) != null) {
			m_Predecessors.get(dest).remove(src);
			if (m_Predecessors.get(dest).size() == 0) {
				m_Predecessors.remove(dest);
			}
		}
	}

	/**
	 * Removes a given {@link SpoilerVertex} object from the game graph.
	 * 
	 * @param vertex
	 *            The vertex to remove
	 */
	protected void removeSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		m_SpoilerVertices.remove(vertex);
		m_BuechiStatesToGraphSpoilerVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.isB(), null);
	}

	/**
	 * Sets the current global infinity bound.<br/>
	 * For more information see {@link #getGlobalInfinity()}.
	 * 
	 * @param globalInfinity
	 *            The number to set
	 */
	protected void setGlobalInfinity(final int globalInfinity) {
		m_GlobalInfinity = globalInfinity;
	}
}
