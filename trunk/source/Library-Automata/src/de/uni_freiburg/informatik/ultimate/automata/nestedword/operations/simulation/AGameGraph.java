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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.VertexValueContainer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorSubSummaryChoiceVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerSubSummaryPriorityVertex;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Abstract class for game graphs which are needed for simulation calculation.
 * <br/>
 * <br/>
 * A game graph represents a game played by <i>Spoiler</i> and <i>Duplicator</i>
 * on an original buechi automaton.<br/>
 * <i>Spoiler</i> tries to build an accepting word <i>Duplicator</i> can not
 * reproduce. If <i>Spoiler</i> fails we say <b>q1 simulates q0</b> if
 * <i>Spoilers</i> starting state was q0 and <i>Duplicators</i> q1.<br/>
 * <br/>
 * The exact winning conditions are determined by special instances of graphs
 * which should extend this class.<br/>
 * Given such an instance a game graph needs to generate itself out of a buechi
 * automaton and be able to generate a reduced buechi automaton as a result of a
 * so called simulation.<br/>
 * This game graph class is also capable of undoing made changes by using the
 * {@link #undoChanges(GameGraphChanges) undoChanges} method and maintaining a
 * {@link GameGraphChanges} object.<br/>
 * <br/>
 * For simulations see {@link ASimulation}.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public abstract class AGameGraph<LETTER, STATE> {
	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomaton<LETTER, STATE> mBuechi;
	/**
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(State of spoiler or q0, Letter spoiler used before, State of
	 * duplicator or q1, bit)</b>.
	 */
	private final NestedMap4<STATE, STATE, LETTER, Boolean, DuplicatorVertex<LETTER, STATE>> mBuechiStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects
	 * by using their representation:<br/>
	 * <b>(State of spoiler or q0, State of duplicator or q1, bit)</b>.
	 */
	private final NestedMap3<STATE, STATE, Boolean, SpoilerVertex<LETTER, STATE>> mBuechiStatesToGraphSpoilerVertex;
	/**
	 * Set of all {@link DuplicatorVertex} objects the game graph holds.
	 */
	private final HashSet<DuplicatorVertex<LETTER, STATE>> mDuplicatorVertices;
	/**
	 * The upper bound which, as counter interpreted, represents at which point
	 * one can be sure that vertices with priority 1 can be visited infinite
	 * times without visiting priority 0.<br/>
	 * In general this is the <b>number of vertices with priority 1 plus 1</b>.
	 */
	private int mGlobalInfinity;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final ILogger mLogger;
	/**
	 * Holds information about the performance of the simulation after usage.
	 */
	private SimulationPerformance mPerformance;
	/**
	 * Data structure that allows a fast access to predecessors of a given
	 * vertex in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> mPredecessors;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer mProgressTimer;
	/**
	 * Data structure that allows a fast access to push-over predecessors of a
	 * given vertex in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> mPushOverPredecessors;
	/**
	 * Data structure that allows a fast access to push-over successors of a
	 * given vertex in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> mPushOverSuccessors;
	/**
	 * Service object used by the framework.
	 */
	private final AutomataLibraryServices mServices;
	/**
	 * Set of all {@link SpoilerVertex} objects the game graph holds.
	 */
	private final HashSet<SpoilerVertex<LETTER, STATE>> mSpoilerVertices;
	/**
	 * State factory used for state creation.
	 */
	private final IMergeStateFactory<STATE> mStateFactory;
	/**
	 * Data structure that allows a fast access to successors of a given vertex
	 * in the game graph.
	 */
	private final HashMap<Vertex<LETTER, STATE>, HashSet<Vertex<LETTER, STATE>>> mSuccessors;

	/**
	 * Creates a new game graph object that initializes all needed data
	 * structures.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            State factory used for state creation.
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated. It must not have any dead ends.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public AGameGraph(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final IProgressAwareTimer progressTimer, final ILogger logger,
			final INestedWordAutomaton<LETTER, STATE> buechi) throws AutomataOperationCanceledException {
		// We assume the automaton has no dead ends, this is a requirement for
		// the algorithm to work correctly.
		mBuechi = buechi;

		mServices = services;
		mProgressTimer = progressTimer;
		mLogger = logger;
		mStateFactory = stateFactory;
		mDuplicatorVertices = new HashSet<>();
		mSpoilerVertices = new HashSet<>();
		mSuccessors = new HashMap<>();
		mPushOverSuccessors = new HashMap<>();
		mPredecessors = new HashMap<>();
		mPushOverPredecessors = new HashMap<>();
		mBuechiStatesToGraphSpoilerVertex = new NestedMap3<>();
		mBuechiStatesToGraphDuplicatorVertex = new NestedMap4<>();
		mGlobalInfinity = 0;
		mPerformance = null;
	}

	/**
	 * Adds a given {@link DuplicatorVertex} object to the game graph.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	public void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		mDuplicatorVertices.add(vertex);
		mBuechiStatesToGraphDuplicatorVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.getLetter(), vertex.isB(),
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
	public void addEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (!mSuccessors.containsKey(src)) {
			mSuccessors.put(src, new HashSet<>());
		}
		mSuccessors.get(src).add(dest);

		// Update predecessor information
		if (!mPredecessors.containsKey(dest)) {
			mPredecessors.put(dest, new HashSet<>());
		}
		mPredecessors.get(dest).add(src);
	}

	/**
	 * Adds a given push-over edge, represented by its source and destination,
	 * to the game graph.
	 * 
	 * @param src
	 *            Source of the push-over edge
	 * @param dest
	 *            Destination of the push-over edge
	 */
	public void addPushOverEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (!mPushOverSuccessors.containsKey(src)) {
			mPushOverSuccessors.put(src, new HashSet<>());
		}
		mPushOverSuccessors.get(src).add(dest);

		// Update predecessor information
		if (!mPushOverPredecessors.containsKey(dest)) {
			mPushOverPredecessors.put(dest, new HashSet<>());
		}
		mPushOverPredecessors.get(dest).add(src);
	}

	/**
	 * Adds a given {@link SpoilerVertex} object to the game graph.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	public void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		mSpoilerVertices.add(vertex);
		mBuechiStatesToGraphSpoilerVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.isB(), vertex);
	}

	/**
	 * Generates a possible reduced buechi automaton by using the current state
	 * of the game graph that may hold information, usable for reduction,
	 * generated by an {@link ASimulation}.
	 * 
	 * @return A possible reduced buechi automaton
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public abstract INestedWordAutomaton<LETTER, STATE> generateAutomatonFromGraph()
			throws AutomataOperationCanceledException;

	/**
	 * Generates the game graph out of an original buechi automaton. The graph
	 * represents a game, see {@link AGameGraph}.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public abstract void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException;

	/**
	 * Gets the amount of edges the game graph has. The method computes the
	 * number at method-call, which takes time linear in the size of the game
	 * graph.
	 * 
	 * @return The amount of edges the game graph has
	 */
	public int getAmountOfEdges() {
		int amountOfEdges = 0;
		for (final HashSet<Vertex<LETTER, STATE>> successors : mSuccessors.values()) {
			amountOfEdges += successors.size();
		}
		return amountOfEdges;
	}

	/**
	 * Gets the underlying automaton.
	 * 
	 * @return The underlying automaton.
	 */
	public INestedWordAutomaton<LETTER, STATE> getAutomaton() {
		return mBuechi;
	}

	/**
	 * Gets the size of the underlying automaton.
	 * 
	 * @return The size of the underlying automaton.
	 */
	public int getAutomatonSize() {
		return mBuechi.size();
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
		return mBuechiStatesToGraphDuplicatorVertex.get(q0, q1, a, bit);
	}

	/**
	 * Gets an unmodifiable set of all {@link DuplicatorVertex} objects the game
	 * graph has.
	 * 
	 * @return An unmodifiable set of all {@link DuplicatorVertex} objects the
	 *         game graph has.
	 */
	public Set<DuplicatorVertex<LETTER, STATE>> getDuplicatorVertices() {
		return Collections.unmodifiableSet(mDuplicatorVertices);
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
		return mGlobalInfinity;
	}

	/**
	 * Gets the internal used field for duplicator vertices. <b>Use with
	 * caution!</b> By modifying this field the game graph may get messed up.
	 * 
	 * @return The internal used field for duplicator vertices.
	 */
	public HashSet<DuplicatorVertex<LETTER, STATE>> getInternalDuplicatorVerticesField() {
		return mDuplicatorVertices;
	}

	/**
	 * Gets the internal used field for spoiler vertices. <b>Use with
	 * caution!</b> By modifying this field the game graph may get messed up.
	 * 
	 * @return The internal used field for spoiler vertices.
	 */
	public HashSet<SpoilerVertex<LETTER, STATE>> getInternalSpoilerVerticesField() {
		return mSpoilerVertices;
	}

	/**
	 * Gets an unmodifiable set of all {@link Vertex} objects the game graph has
	 * that do have successors, also known as non dead end.
	 * 
	 * @return An unmodifiable set of all {@link Vertex} objects the game graph
	 *         has that do have successors.
	 */
	public Set<Vertex<LETTER, STATE>> getNonDeadEndVertices() {
		return Collections.unmodifiableSet(mSuccessors.keySet());
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
			return Collections.unmodifiableSet(mPredecessors.get(vertex));
		} else {
			return null;
		}
	}

	/**
	 * Gets the priority of a given vertex.
	 * <p>
	 * Throws an IllegalArgumentException If the given vertex is <tt>null</tt>.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return The priority of the given vertex
	 */
	public int getPriority(final Vertex<LETTER, STATE> vertex) {
		if (vertex == null) {
			throw new IllegalArgumentException("The given vertex must not be null.");
		}
		return vertex.getPriority();
	}

	/**
	 * Gets an unmodifiable set of all push-over predecessors a given
	 * {@link Vertex} has or <tt>null</tt> if it has no.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return An unmodifiable set of all push-over predecessors the given
	 *         {@link Vertex} has or <tt>null</tt> if it has no.
	 */
	public Set<Vertex<LETTER, STATE>> getPushOverPredecessors(final Vertex<LETTER, STATE> vertex) {
		if (hasPushOverPredecessors(vertex)) {
			return Collections.unmodifiableSet(mPushOverPredecessors.get(vertex));
		} else {
			return null;
		}
	}

	/**
	 * Gets an unmodifiable set of all push-over successors a given
	 * {@link Vertex} has or <tt>null</tt> if it has no.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return An unmodifiable set of all push-over successors the given
	 *         {@link Vertex} has or <tt>null</tt> if it has no.
	 */
	public Set<Vertex<LETTER, STATE>> getPushOverSuccessors(final Vertex<LETTER, STATE> vertex) {
		if (hasPushOverSuccessors(vertex)) {
			return Collections.unmodifiableSet(mPushOverSuccessors.get(vertex));
		} else {
			return null;
		}
	}

	/**
	 * Gets the service object used by the Ultimate framework.
	 * 
	 * @return The service object used by the Ultimate framework.
	 */
	public AutomataLibraryServices getServices() {
		return mServices;
	}

	/**
	 * Gets the size of the game graph which is the number of all vertices.
	 * 
	 * @return The size of the game graph which is the number of all vertices.
	 */
	public int getSize() {
		return mSpoilerVertices.size() + mDuplicatorVertices.size();
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
		return mBuechiStatesToGraphSpoilerVertex.get(q0, q1, bit);
	}

	/**
	 * Gets an unmodifiable set of all {@link SpoilerVertex} objects the game
	 * graph has.
	 * 
	 * @return An unmodifiable set of all {@link SpoilerVertex} objects the game
	 *         graph has.
	 */
	public Set<SpoilerVertex<LETTER, STATE>> getSpoilerVertices() {
		return Collections.unmodifiableSet(mSpoilerVertices);
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
			return Collections.unmodifiableSet(mSuccessors.get(vertex));
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
		final HashSet<Vertex<LETTER, STATE>> result = new HashSet<>(mSpoilerVertices);
		result.addAll(mDuplicatorVertices);
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
		return mPredecessors.containsKey(vertex);
	}

	/**
	 * If a given {@link Vertex} has push-over predecessor vertices or not.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the vertex has push-over predecessors, false if not.
	 */
	public boolean hasPushOverPredecessors(final Vertex<LETTER, STATE> vertex) {
		return mPushOverPredecessors.containsKey(vertex);
	}

	/**
	 * If a given {@link Vertex} has push-over successor vertices or not.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the vertex has push-over successors, false if not.
	 */
	public boolean hasPushOverSuccessors(final Vertex<LETTER, STATE> vertex) {
		return mPushOverSuccessors.containsKey(vertex);
	}

	/**
	 * If a given {@link Vertex} has successor vertices or not.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the vertex has successors, false if not.
	 */
	public boolean hasSuccessors(final Vertex<LETTER, STATE> vertex) {
		return mSuccessors.containsKey(vertex);
	}

	/**
	 * Increases the current global infinity bound by one.<br/>
	 * For more information see {@link #getGlobalInfinity()}.
	 */
	public void increaseGlobalInfinity() {
		mGlobalInfinity++;
	}

	/**
	 * Removes a given {@link DuplicatorVertex} object from the game graph.
	 * 
	 * @param vertex
	 *            The vertex to remove
	 */
	public void removeDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		mDuplicatorVertices.remove(vertex);
		mBuechiStatesToGraphDuplicatorVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.getLetter(), vertex.isB(),
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
	public void removeEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (mSuccessors.get(src) != null) {
			mSuccessors.get(src).remove(dest);
			if (mSuccessors.get(src).size() == 0) {
				mSuccessors.remove(src);
			}
		}

		// Update predecessor information
		if (mPredecessors.get(dest) != null) {
			mPredecessors.get(dest).remove(src);
			if (mPredecessors.get(dest).size() == 0) {
				mPredecessors.remove(dest);
			}
		}
	}

	/**
	 * Removes a given push-over edge, represented by its source and
	 * destination, from the game graph.
	 * 
	 * @param src
	 *            Source of the edge
	 * @param dest
	 *            Destination of the edge
	 */
	public void removePushOverEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		// Update successor information
		if (mPushOverSuccessors.get(src) != null) {
			mPushOverSuccessors.get(src).remove(dest);
			if (mPushOverSuccessors.get(src).size() == 0) {
				mPushOverSuccessors.remove(src);
			}
		}

		// Update predecessor information
		if (mPushOverPredecessors.get(dest) != null) {
			mPushOverPredecessors.get(dest).remove(src);
			if (mPushOverPredecessors.get(dest).size() == 0) {
				mPushOverPredecessors.remove(dest);
			}
		}
	}

	/**
	 * Removes a given {@link SpoilerVertex} object from the game graph.
	 * 
	 * @param vertex
	 *            The vertex to remove
	 */
	public void removeSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		mSpoilerVertices.remove(vertex);
		mBuechiStatesToGraphSpoilerVertex.put(vertex.getQ0(), vertex.getQ1(), vertex.isB(), null);
	}

	/**
	 * Sets the performance object of the corresponding simulation.
	 * 
	 * @param simulationPerformance
	 *            Simulation performance to set.
	 */
	public void setSimulationPerformance(final SimulationPerformance simulationPerformance) {
		mPerformance = simulationPerformance;
	}

	/**
	 * Returns the graph in the <tt>ats</tt> file format. This can be used for
	 * example to visualize it via the toolchain.
	 * 
	 * @return Representation of the graph in the <tt>ats</tt> file format.
	 */
	public String toAtsFormat() {
		final StringBuilder result = new StringBuilder();
		final String lineSeparator = System.lineSeparator();
		// Header
		result.append("NestedWordAutomaton nwa = (");
		result.append(lineSeparator + "\tcallAlphabet = { },");
		result.append(lineSeparator + "\tinternalAlphabet = {a},");
		result.append(lineSeparator + "\treturnAlphabet = { },");

		// States
		result.append(lineSeparator + "\tstates = {");
		final StringBuilder states = new StringBuilder();
		boolean isFirstVertex = true;
		// Creates states in the following format:
		// {"state1" "state2" "state3" ...}
		for (final Vertex<LETTER, STATE> vertex : getVertices()) {
			if (!isFirstVertex) {
				states.append(" ");
			}
			states.append("\"").append(vertex.getName()).append("\"");
			isFirstVertex = false;
		}

		result.append(states.toString()).append("},");
		result.append(lineSeparator + "\tinitialStates = {" + states.toString() + "},");
		result.append(lineSeparator + "\tfinalStates = { },");

		// Transitions
		result.append(lineSeparator + "\tcallTransitions = { },");
		result.append(lineSeparator + "\tinternalTransitions = {");

		for (final Vertex<LETTER, STATE> pred : getVertices()) {
			if (!hasSuccessors(pred)) {
				continue;
			}
			for (final Vertex<LETTER, STATE> succ : getSuccessors(pred)) {
				// Creates a transition in the following format:
				// ("pred" "a" "succ")
				result.append(lineSeparator).append("\t\t(\"").append(pred.getName()).append("\" \"a\" \"")
						.append(succ.getName()).append("\")");
			}
		}

		result.append(lineSeparator + "\t},");
		result.append(lineSeparator + "\treturnTransitions = {}");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder();
		final String lineSeparator = System.lineSeparator();
		// Header
		result.append("GameGraph gg = (");

		// Vertices
		result.append(lineSeparator + "\tSpoilerVertices = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.isB() + ", " + vertex.getQ0() + ", " + vertex.getQ1()
					+ "), p:" + getPriority(vertex) + ">");
		}
		result.append(lineSeparator + "\t},");
		result.append(lineSeparator + "\tDuplicatorVertices = {");
		for (final DuplicatorVertex<LETTER, STATE> vertex : getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.isB() + ", " + vertex.getQ0() + ", " + vertex.getQ1() + ", "
					+ vertex.getLetter() + "), p:" + getPriority(vertex) + ">");
		}
		result.append(lineSeparator + "\t},");

		// Edges
		result.append(lineSeparator + "\tedges = {");
		for (final Vertex<LETTER, STATE> vertex : getNonDeadEndVertices()) {
			for (final Vertex<LETTER, STATE> succ : getSuccessors(vertex)) {
				result.append(lineSeparator + "\t\t(" + vertex.isB() + ", " + vertex.getQ0() + ", " + vertex.getQ1());
				if (vertex instanceof DuplicatorVertex) {
					final DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex =
							(DuplicatorVertex<LETTER, STATE>) vertex;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")");
				if ((vertex instanceof SpoilerSubSummaryPriorityVertex)
						|| (vertex instanceof DuplicatorSubSummaryChoiceVertex)) {
					result.append(vertex.getClass().getSimpleName());
				}
				result.append("\t--> (" + succ.isB() + ", " + succ.getQ0() + ", " + succ.getQ1());
				if (succ instanceof DuplicatorVertex) {
					final DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex =
							(DuplicatorVertex<LETTER, STATE>) succ;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")");
				if ((succ instanceof SpoilerSubSummaryPriorityVertex)
						|| (succ instanceof DuplicatorSubSummaryChoiceVertex)) {
					result.append(succ.getClass().getSimpleName());
				}
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
		final NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedEdges =
				changes.getChangedEdges();
		for (final Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedEdge : changedEdges
				.entrySet()) {
			final Vertex<LETTER, STATE> src = changedEdge.getFirst();
			final Vertex<LETTER, STATE> dest = changedEdge.getSecond();
			final EGameGraphChangeType type = changedEdge.getThird();
			// If added before, remove and vice versa
			if (type.equals(EGameGraphChangeType.ADDITION)) {
				removeEdge(src, dest);
			} else if (type.equals(EGameGraphChangeType.REMOVAL)) {
				addEdge(src, dest);
			}
		}

		// Undo push-over edge changes
		final NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedPushOverEdges =
				changes.getChangedPushOverEdges();
		for (final Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedPushOverEdge : changedPushOverEdges
				.entrySet()) {
			final Vertex<LETTER, STATE> src = changedPushOverEdge.getFirst();
			final Vertex<LETTER, STATE> dest = changedPushOverEdge.getSecond();
			final EGameGraphChangeType type = changedPushOverEdge.getThird();
			// If added before, remove and vice versa
			if (type.equals(EGameGraphChangeType.ADDITION)) {
				removePushOverEdge(src, dest);
			} else if (type.equals(EGameGraphChangeType.REMOVAL)) {
				addPushOverEdge(src, dest);
			}
		}

		// Undo vertex changes
		final HashMap<Vertex<LETTER, STATE>, EGameGraphChangeType> changedVertices = changes.getChangedVertices();
		for (final Entry<Vertex<LETTER, STATE>, EGameGraphChangeType> changedVertex : changedVertices.entrySet()) {
			final Vertex<LETTER, STATE> vertex = changedVertex.getKey();
			final EGameGraphChangeType type = changedVertex.getValue();
			// If added before, remove and vice versa
			if (type.equals(EGameGraphChangeType.ADDITION)) {
				if (vertex.isDuplicatorVertex()) {
					removeDuplicatorVertex((DuplicatorVertex<LETTER, STATE>) vertex);
				} else if (vertex.isSpoilerVertex()) {
					removeSpoilerVertex((SpoilerVertex<LETTER, STATE>) vertex);
				}
			} else if (type.equals(EGameGraphChangeType.REMOVAL)) {
				if (vertex.isDuplicatorVertex()) {
					addDuplicatorVertex((DuplicatorVertex<LETTER, STATE>) vertex);
				} else if (vertex.isSpoilerVertex()) {
					addSpoilerVertex((SpoilerVertex<LETTER, STATE>) vertex);
				}
			}
		}

		// Undo vertex value changes
		final HashMap<Vertex<LETTER, STATE>, VertexValueContainer> changedVertexValues =
				changes.getRememberedVertexValues();
		for (final Entry<Vertex<LETTER, STATE>, VertexValueContainer> changedValues : changedVertexValues.entrySet()) {
			final Vertex<LETTER, STATE> vertex = changedValues.getKey();
			final VertexValueContainer values = changedValues.getValue();
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
	 * Verifies the validity of a given automaton. If the automaton is not valid it throws an
	 * {@link IllegalArgumentException}.
	 * 
	 * @param automaton
	 *            Automaton to verify validity
	 */
	public void verifyAutomatonValidity(final INestedWordAutomaton<LETTER, STATE> automaton) {
		if (!automaton.getCallAlphabet().isEmpty() || !automaton.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException(
					"The inputed automaton is no Buechi-automaton. It must have an empty call and return alphabet.");
		}
	}

	/**
	 * Gets the logger used by the Ultimate framework.
	 * 
	 * @return The logger used by the Ultimate framework.
	 */
	protected ILogger getLogger() {
		return mLogger;
	}

	/**
	 * Gets the timer used for responding to timeouts and operation
	 * cancellation.
	 * 
	 * @return The timer used for responding to timeouts and operation
	 *         cancellation.
	 */
	protected IProgressAwareTimer getProgressTimer() {
		return mProgressTimer;
	}

	/**
	 * Gets the performance object of the corresponding simulation.
	 * 
	 * @return The performance object of the corresponding simulation.
	 */
	protected SimulationPerformance getSimulationPerformance() {
		return mPerformance;
	}

	/**
	 * Gets the state factory used for state creation.
	 * 
	 * @return The state factory used for state creation
	 */
	protected IMergeStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	/**
	 * Sets the current global infinity bound.<br/>
	 * For more information see {@link #getGlobalInfinity()}.
	 * 
	 * @param globalInfinity
	 *            The number to set
	 */
	protected void setGlobalInfinity(final int globalInfinity) {
		mGlobalInfinity = globalInfinity;
	}
}
