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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Simulation that realizes <b>fair simulation</b> for reduction of a given
 * buechi automaton.<br/>
 * Once created it starts the simulation, results can then be get by using
 * {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see {@link FairGameGraph}.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class FairSimulation<LETTER, STATE> extends ASimulation<LETTER, STATE> {

	/**
	 * Saves a change on the <i>BEff value</i> of a given vertex in the current
	 * {@link GameGraphChanges} object if there currently is no such value
	 * stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void saveBEffChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getBEff() && !changes.hasBEffEntry(vertex)) {
			changes.rememberBEffVertex(vertex, oldValue);
		}
	}

	/**
	 * Saves a change on the <i>C value</i> of a given vertex in the current
	 * {@link GameGraphChanges} object if there currently is no such value
	 * stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void saveCChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getC() && !changes.hasCEntry(vertex)) {
			changes.rememberCVertex(vertex, oldValue);
		}
	}

	/**
	 * Saves a change on the <i>Progress measure value</i> of a given vertex in
	 * the current {@link GameGraphChanges} object if there currently is no such
	 * value stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void savePmChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getPM(null, 0) && !changes.hasPmEntry(vertex)) {
			changes.rememberPmVertex(vertex, oldValue);
		}
	}

	/**
	 * If the simulation process itself should log detailed debugging
	 * information.
	 */
	private final boolean debugSimulation = false;
	/**
	 * True if currently attempting to do changes on the game graph, false if
	 * not. Used to tell {@link #efficientLiftingAlgorithm(int, Set)} to re use
	 * information of previous simulation runs and to store information about
	 * changes in order to be able to undo them.
	 */
	private boolean m_AttemptingChanges;
	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	/**
	 * The game graph changes object that is currently used to store information
	 * about made changes. Used by {@link #efficientLiftingAlgorithm(int, Set)}
	 * to store its changes since it can not access it by another way because of
	 * the interface. Assign <tt>null</tt> to indicate that changes should not
	 * be stored.
	 */
	private GameGraphChanges<LETTER, STATE> m_CurrentChanges;
	/**
	 * Game graph that is used for simulation calculation.
	 */
	private final FairGameGraph<LETTER, STATE> m_Game;
	/**
	 * Copy of {@link AGameGraph#getGlobalInfinity()} for faster access.
	 */
	private final int m_GlobalInfinity;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * Stores all currently known {@link SpoilerVertex} objects that indicate
	 * simulation is not possible and are non trivial. This are vertices with a
	 * progress measure that reached infinity and where q1 is not equals q2 for
	 * the representation (q1, q2) because this are trivial simulations.<br/>
	 * The set is used to abort the simulation early whenever a previous
	 * possible simulation gets removed due to a game graph change.
	 */
	private Set<SpoilerVertex<LETTER, STATE>> m_NotSimulatingNonTrivialVertices;
	/**
	 * Contains all vertices that are currently poked from a neighbor SCC,
	 * Strongly Connected Component, if used.<br/>
	 * Poked vertices need to be added to the working list and calculate their
	 * update by ignoring the bounds of its own SCC as soon as its their turn
	 * because a successor of a neighboring SCC has reached infinity.
	 */
	private HashSet<Vertex<LETTER, STATE>> m_pokedFromNeighborSCC;
	/**
	 * True if the simulation was aborted early because its already known that
	 * the underlying language did change, false if not.
	 */
	private boolean m_SimulationWasAborted;

	/**
	 * Counts the amount of simulation steps needed to fully finish simulation.
	 * <br/>
	 * Can be used for runtime debugging.
	 */
	private int m_StepCounter;

	/**
	 * Creates a new fair simulation that tries to reduce the given buechi
	 * automaton using <b>fair simulation</b>.<br/>
	 * After construction the simulation starts and results can be get by using
	 * {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework.
	 * @param buechi
	 *            The buechi automaton to reduce with no dead ends nor with
	 *            duplicate transitions
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairSimulation(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi, final boolean useSCCs,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, useSCCs, stateFactory);

		m_Buechi = buechi;
		m_Logger = getServiceProvider().getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_pokedFromNeighborSCC = null;
		m_NotSimulatingNonTrivialVertices = new HashSet<>();
		m_CurrentChanges = null;

		getLogger().debug("Starting generation of Fair Game Graph...");
		m_Game = new FairGameGraph<>(services, buechi);

		m_GlobalInfinity = m_Game.getGlobalInfinity();

		m_AttemptingChanges = false;
		m_SimulationWasAborted = false;

		doSimulation();
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
		result.append("FairSimulationResults fsr = (");

		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + isUsingSCCs());
		result.append(lineSeparator + "\tglobalInfinity = " + m_GlobalInfinity);
		result.append(lineSeparator + "\tstepCounter = " + m_StepCounter);
		result.append(lineSeparator + "\tbuechi size before = " + m_Buechi.size() + " states");
		if (getResult() != null) {
			result.append(lineSeparator + "\tbuechi size after = " + getResult().size() + " states");
		}

		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			int localInfinity = m_GlobalInfinity;
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), pm:"
					+ vertex.getPM(null, m_GlobalInfinity) + " of " + localInfinity + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			int localInfinity = m_GlobalInfinity;
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), pm:" + vertex.getPM(null, m_GlobalInfinity) + " of " + localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");

		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), bnm:"
					+ vertex.getBEff() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), bnm:" + vertex.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			result.append(
					lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), nc:" + vertex.getC() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Adds a given vertex to the working list and updates its own working list
	 * flag.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	private void addVertexToWorkingList(final Vertex<LETTER, STATE> vertex) {
		getWorkingList().add(vertex);
		vertex.setInWL(true);
	}

	/**
	 * Attempts the simulated merge of two given buechi states and returns
	 * whether the change is valid or not.
	 * 
	 * @param firstState
	 *            First state to merge
	 * @param secondState
	 *            Second state to merge
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private FairGameGraphChanges<LETTER, STATE> attemptMerge(final STATE firstState, final STATE secondState)
			throws OperationCanceledException {
		FairGameGraphChanges<LETTER, STATE> changes = m_Game.equalizeBuechiStates(firstState, secondState);

		return validateChange(changes);
	}

	/**
	 * Attempts the simulated removal of an buechi transition and returns
	 * whether the change is valid or not.
	 * 
	 * @param src
	 *            Source of the transition
	 * @param a
	 *            Letter of the transition
	 * @param dest
	 *            Destination of the transition
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private FairGameGraphChanges<LETTER, STATE> attemptTransitionRemoval(final STATE src, final LETTER a,
			final STATE dest) throws OperationCanceledException {
		FairGameGraphChanges<LETTER, STATE> changes = m_Game.removeBuechiTransition(src, a, dest);

		return validateChange(changes);
	}

	/**
	 * Does a single simulation calculation run. After it has finished the
	 * progress measure of all game graph vertices can be used to determine a
	 * simulation relation used for buechi reduction.<br/>
	 * Can also be used to validate a attempted change, if simulation did not
	 * get aborted the change is valid.
	 * 
	 * @param changes
	 *            Object to store made changes in, <tt>null</tt> if changes
	 *            should not get stored
	 * @return False if simulation was aborted because the underlying language
	 *         changed, true if not.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private boolean doSingleSimulation(final GameGraphChanges<LETTER, STATE> changes)
			throws OperationCanceledException {
		if (isUsingSCCs()) {
			m_pokedFromNeighborSCC = new HashSet<>();
			DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>> sccFactory = new DefaultStronglyConnectedComponentFactory<>();
			GameGraphSuccessorProvider<LETTER, STATE> succProvider = new GameGraphSuccessorProvider<>(m_Game);
			setSccComp(new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					getLogger(), succProvider, sccFactory, m_Game.getSize(), m_Game.getVertices()));

			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter = new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					getSccComp().getSCCs()).iterator();

			while (iter.hasNext()) {
				StronglyConnectedComponent<Vertex<LETTER, STATE>> scc = iter.next();
				iter.remove();

				int infinityOfSCC = calculateInfinityOfSCC(scc);

				m_CurrentChanges = changes;
				efficientLiftingAlgorithm(infinityOfSCC, scc.getNodes());
				if (m_SimulationWasAborted) {
					return false;
				}
			}
		} else {
			m_CurrentChanges = changes;
			efficientLiftingAlgorithm(m_GlobalInfinity, null);
			if (m_SimulationWasAborted) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Initializes the simulation by adding the correct vertices to the working
	 * list and initializing their corresponding values.
	 * 
	 * @param localInfinity
	 *            The local infinity bound of the used SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The currently for simulation used SCC or <tt>null</tt> if not
	 *            used
	 */
	private void initSimulation(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		m_SimulationWasAborted = false;
		createWorkingList();
		// Do not forget to reset the working list flag of all vertices to false
		// This is needed since a simulation can be aborted
		// before working all vertices
		if (isUsingSCCs()) {
			for (Vertex<LETTER, STATE> vertex : scc) {
				initWorkingListAndCWithVertex(vertex, localInfinity, scc);
			}
		} else {
			for (SpoilerVertex<LETTER, STATE> spoilerVertex : m_Game.getSpoilerVertices()) {
				initWorkingListAndCWithVertex(spoilerVertex, localInfinity, scc);
			}
			for (DuplicatorVertex<LETTER, STATE> duplicatorVertex : m_Game.getDuplicatorVertices()) {
				initWorkingListAndCWithVertex(duplicatorVertex, localInfinity, scc);
			}
		}
	}

	/**
	 * Initializes a given vertex for the current simulation calculation by
	 * possibly adding it to the working list and initializing its values.<br/>
	 * Used by {@link #initSimulation(int, Set)}.
	 * 
	 * @param vertex
	 *            Vertex to initialize
	 * @param localInfinity
	 *            The local infinity bound of the used SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The currently for simulation used SCC or <tt>null</tt> if not
	 *            used
	 */
	private void initWorkingListAndCWithVertex(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		// TODO Find out what vertices are really needed for the working list

		// Small note for debugging: If simulation calculates a wrong result
		// this, in most cases, is because there are important vertices missing
		// in the working list. Cross check by adding 'true' to the if-clause
		// which adds all vertices to the working list (inefficient but result
		// could then be correct).
		boolean isDeadEnd = !m_Game.hasSuccessors(vertex);
		boolean hasPriorityOne = vertex.getPriority() == 1;
		boolean isPokedVertex = isUsingSCCs() && m_pokedFromNeighborSCC.contains(vertex);
		boolean isNonTrivialAddedVertex = m_AttemptingChanges && m_CurrentChanges != null
				&& m_CurrentChanges.isAddedVertex(vertex) && vertex.getPriority() != 0;
		boolean isVertexInvolvedInEdgeChanges = m_AttemptingChanges && m_CurrentChanges != null
				&& m_CurrentChanges.isVertexInvolvedInEdgeChanges(vertex);

		// Possibly add vertex to working list
		if (isDeadEnd || hasPriorityOne || isPokedVertex || isNonTrivialAddedVertex || isVertexInvolvedInEdgeChanges) {
			addVertexToWorkingList(vertex);
		} else {
			// Reset working list flag of vertex since it can be true from an
			// previous simulation abort
			vertex.setInWL(false);
		}

		// Possibly initialize C value of vertex
		if (isUsingSCCs()) {
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			// Ignore bounds of own SCC if vertex was poked
			if (m_pokedFromNeighborSCC.contains(vertex)) {
				usedSCCForNeighborCalculation = null;
			}
			int oldC = vertex.getC();
			vertex.setC(calcNghbCounter(vertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(vertex, oldC, m_CurrentChanges);
		} else if (!isDeadEnd) {
			boolean isFirstRun = !m_AttemptingChanges;
			boolean wasNotInitialized = vertex.getC() == 0;

			if (isFirstRun || wasNotInitialized) {
				int oldC = vertex.getC();
				vertex.setC(m_Game.getSuccessors(vertex).size());
				saveCChange(vertex, oldC, m_CurrentChanges);
			}
		}
	}

	/**
	 * Returns {@link SpoilerVertex} object that define states <b>(q0, q1)</b>
	 * which are candidates for merge.<br/>
	 * <br/>
	 * To be more precise, <b>(q0, q1)</b> if <b>q1 fair simulates q0</b> and
	 * <b>q0 fair simulates q1</b> which is indicated by a progress measure less
	 * than global infinity. Such states may can be merged with not changing the
	 * language.
	 * 
	 * @return Buechi states that are candidates for merge.
	 */
	private Set<SpoilerVertex<LETTER, STATE>> mergeCandidates() {
		Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = new HashSet<>();
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = m_Game.getSpoilerVertices();
		Set<SpoilerVertex<LETTER, STATE>> workedPairs = new HashSet<>();
		for (SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, m_GlobalInfinity) < m_GlobalInfinity) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}
				// Found a one-directed fair simulating pair
				boolean pairIsNew = workedPairs.add(vertex);

				if (pairIsNew && workedPairs.contains(m_Game.getSpoilerVertex(vertex.getQ1(), vertex.getQ0(), false))) {
					// Found a two-directed fair simulating pair
					mergeCandidates.add(vertex);
				}
			}
		}
		return mergeCandidates;
	}

	/**
	 * Retrieves and removes the head of the working list. Also updates the
	 * working list flag of the vertex.
	 * 
	 * @return The head of the working list, or <tt>null</tt> if it is empty.
	 */
	private Vertex<LETTER, STATE> pollVertexFromWorkingList() {
		Vertex<LETTER, STATE> polledVertex = getWorkingList().poll();
		if (polledVertex != null) {
			polledVertex.setInWL(false);
		}
		return polledVertex;
	}

	/**
	 * Returns buechi transitions that are candidates for removal.<br/>
	 * <br/>
	 * To be more precise, transitions <b>q1 -a-> q2</b> where <b>q1 -a-> q3</b>
	 * exists and <b>q3 fair simulates q2</b>. Such transitions may be redundant
	 * and not change the language if removed.
	 * 
	 * @param exclusiveSet
	 *            Set of {@link SpoilerVertex} objects <b>(q2, q3)</b> that
	 *            define simulations that should not get considered for
	 *            candidate generation. In general this are vertices that get
	 *            merged, such transitions would get removed in the merging
	 *            process anyway.
	 * @return Buechi transitions that are candidates for removal.
	 */
	private NestedMap2<STATE, LETTER, STATE> transitionCandidates(
			final Set<SpoilerVertex<LETTER, STATE>> exclusiveSet) {
		NestedMap2<STATE, LETTER, STATE> edgeCandidates = new NestedMap2<>();
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = m_Game.getSpoilerVertices();
		for (SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, m_GlobalInfinity) < m_GlobalInfinity && !exclusiveSet.contains(vertex)) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}

				// Searching for transition
				// q1 -a-> q2 where q1 -a-> q3 and q3 simulating q2
				STATE simulatingState = vertex.getQ1();
				STATE simulatedState = vertex.getQ0();
				for (IncomingInternalTransition<LETTER, STATE> predTrans : m_Buechi
						.internalPredecessors(simulatingState)) {
					STATE src = predTrans.getPred();
					LETTER a = predTrans.getLetter();
					STATE dest = simulatedState;
					if (m_Game.hasBuechiTransition(new Triple<>(src, a, dest))) {
						edgeCandidates.put(src, a, dest);
					}
				}

			}
		}
		return edgeCandidates;
	}

	/**
	 * Validates a given change by re running a single simulation calculation
	 * and comparing its results to the previous.<br/>
	 * If the change is valid <tt>null</tt> gets returned, if not an extended
	 * fair game graph changes object gets returned that includes the previous
	 * changes and also the changes made in the simulation calculation used for
	 * verification.
	 * 
	 * @param changes
	 *            Made changes to validate
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private FairGameGraphChanges<LETTER, STATE> validateChange(FairGameGraphChanges<LETTER, STATE> changes)
			throws OperationCanceledException {
		// Only do simulation if there actually was a change
		boolean wasSuccessful = true;
		if (changes != null) {
			wasSuccessful = doSingleSimulation(changes);
		}

		// Discard changes if language did not change
		// so that they can not be undone.
		if (wasSuccessful) {
			changes = null;
		}

		return changes;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#doSimulation()
	 */
	@Override
	protected void doSimulation() throws OperationCanceledException {
		long startTime = System.currentTimeMillis();
		m_StepCounter = 0;

		// First simulation
		getLogger().debug("Starting first simulation...");
		doSingleSimulation(null);
		getLogger().debug("Ending first simulation.");

		// Merge states
		m_AttemptingChanges = true;
		List<Pair<STATE, STATE>> statesToMerge = new LinkedList<>();
		Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = mergeCandidates();
		Set<SpoilerVertex<LETTER, STATE>> noTransitionCandidates = new HashSet<>();

		getLogger().debug("Size of merge candidates: " + mergeCandidates.size());

		for (SpoilerVertex<LETTER, STATE> mergeCandidate : mergeCandidates) {
			STATE leftState = mergeCandidate.getQ0();
			STATE rightState = mergeCandidate.getQ1();

			// Attempt merge
			FairGameGraphChanges<LETTER, STATE> changes = attemptMerge(leftState, rightState);
			// Undo if language changed, else do not consider
			// pair for transition removal
			if (changes != null) {
				getLogger().debug(
						"Attempted merge for " + leftState + " and " + rightState + " was not successful, undoing...");

				m_Game.undoChanges(changes);
			} else {
				getLogger().debug("Attempted merge for " + leftState + " and " + rightState + " was successful.");
				statesToMerge.add(new Pair<>(leftState, rightState));

				noTransitionCandidates.add(mergeCandidate);
				SpoilerVertex<LETTER, STATE> mirroredCandidate = m_Game.getSpoilerVertex(rightState, leftState, false);
				if (mirroredCandidate != null) {
					noTransitionCandidates.add(mirroredCandidate);
				}
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in doSimulation/attempting merges");
				throw new OperationCanceledException(this.getClass());
			}
		}

		// Remove redundant transitions
		List<Triple<STATE, LETTER, STATE>> transitionsToRemove = new LinkedList<>();
		NestedMap2<STATE, LETTER, STATE> transitionCandidates = transitionCandidates(noTransitionCandidates);

		// keySet is okay for a debugging message because
		// access is cheap, in O(1)
		getLogger().debug("Size of transition candidates is >= " + transitionCandidates.keySet().size());

		for (Triple<STATE, LETTER, STATE> transitionCandidate : transitionCandidates.entrySet()) {
			STATE src = transitionCandidate.getFirst();
			LETTER a = transitionCandidate.getSecond();
			STATE dest = transitionCandidate.getThird();

			// Attempt transition removal
			FairGameGraphChanges<LETTER, STATE> changes = attemptTransitionRemoval(src, a, dest);
			// Undo if language changed, else add transition for removal
			if (changes != null) {
				getLogger().debug("Attempted transition removal for " + src + " -" + a + "-> " + dest
						+ " was not successful, undoing...");
				m_Game.undoChanges(changes);
			} else {
				getLogger().debug(
						"Attempted transition removal for " + src + " -" + a + "-> " + dest + " was successful.");
				transitionsToRemove.add(new Triple<>(src, a, dest));
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in doSimulation/attempting transition removal");
				throw new OperationCanceledException(this.getClass());
			}
		}

		// Pass states to merge and transitions to remove
		m_Game.setStatesToMerge(statesToMerge);
		m_Game.setTransitionsToRemove(transitionsToRemove);

		// Generate the resulting automata
		getLogger().debug("Generating the result automaton...");
		setResult(m_Game.generateBuchiAutomatonFromGraph());

		long duration = System.currentTimeMillis() - startTime;
		getLogger().info((isUsingSCCs() ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds and "
				+ m_StepCounter + " simulation steps.");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#efficientLiftingAlgorithm(int, java.util.Set)
	 */
	@Override
	protected void efficientLiftingAlgorithm(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc)
			throws OperationCanceledException {
		if (debugSimulation) {
			getLogger().debug("Lifting SCC: " + scc);
		}

		// Initialize working list and the C value of the correct vertices
		initSimulation(localInfinity, scc);

		if (debugSimulation) {
			getLogger().debug("WL: " + getWorkingList());
		}

		// Work through the working list until its empty
		while (!getWorkingList().isEmpty()) {
			m_StepCounter++;

			// Poll the current working vertex
			Vertex<LETTER, STATE> workingVertex = pollVertexFromWorkingList();

			if (debugSimulation) {
				getLogger().debug("\tWorking with: " + workingVertex);
			}

			// Ignore bounds of own SCC if vertex was poked
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (isUsingSCCs() && m_pokedFromNeighborSCC.contains(workingVertex)) {
				usedSCCForNeighborCalculation = null;
				if (debugSimulation) {
					getLogger().debug("\t\tVertex was poked.");
				}
			}

			// Remember old progress measure of the working vertex
			int oldProgressMeasure = workingVertex.getPM(scc, m_GlobalInfinity);

			// Update values of the working vertex
			int oldBEff = workingVertex.getBEff();
			workingVertex.setBEff(calcBestNghbMeasure(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveBEffChange(workingVertex, oldBEff, m_CurrentChanges);

			if (debugSimulation) {
				getLogger().debug("\t\tUpdated BEff: " + oldBEff + " -> " + workingVertex.getBEff());
			}

			int oldC = workingVertex.getC();
			workingVertex.setC(calcNghbCounter(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(workingVertex, oldC, m_CurrentChanges);

			if (debugSimulation) {
				getLogger().debug("\t\tUpdated C: " + oldC + " -> " + workingVertex.getC());
			}

			int currentProgressMeasure = increaseVector(workingVertex.getPriority(), workingVertex.getBEff(),
					localInfinity);
			workingVertex.setPM(currentProgressMeasure);
			savePmChange(workingVertex, oldProgressMeasure, m_CurrentChanges);

			if (debugSimulation) {
				getLogger().debug("\t\tUpdated PM: " + oldProgressMeasure + " -> " + currentProgressMeasure);
			}

			// If vertex now defines a non trivial non possible simulation
			if (currentProgressMeasure >= m_GlobalInfinity) {
				if (workingVertex.isSpoilerVertex() && !workingVertex.getQ0().equals(workingVertex.getQ1())) {
					boolean wasAdded = m_NotSimulatingNonTrivialVertices
							.add((SpoilerVertex<LETTER, STATE>) workingVertex);
					if (m_AttemptingChanges && wasAdded) {
						// Abort simulation since progress measure
						// has changed on a non trivial vertex
						// which indicates language change
						m_NotSimulatingNonTrivialVertices.remove((SpoilerVertex<LETTER, STATE>) workingVertex);
						m_SimulationWasAborted = true;

						if (debugSimulation) {
							getLogger().debug("\t\tAborting simulation since " + workingVertex + " reached infinity.");
						}
						return;
					}
				}
			}

			// Skip updating predecessors if there are no
			Set<Vertex<LETTER, STATE>> predVertices = m_Game.getPredecessors(workingVertex);
			if (predVertices == null || predVertices.isEmpty()) {
				continue;
			}

			// Work through its predecessors and possibly add them
			// to the working list since they may be interested in
			// the changes of the working vertex
			for (Vertex<LETTER, STATE> pred : predVertices) {
				if (debugSimulation) {
					getLogger().debug("\t\tWorking pred: " + pred);
				}

				if (pred.isInWL()) {
					// Skip predecessor if already in working list
					continue;
				}

				// If vertex has newly reached localInfinity and predecessor,
				// which is a 1-distance neighbor of SCC, is interested
				boolean pokePossible = false;
				if (isUsingSCCs() && !scc.contains(pred)) {
					boolean hasNewlyReachedInfinity = currentProgressMeasure >= localInfinity
							&& oldProgressMeasure < localInfinity;
					pokePossible = hasNewlyReachedInfinity && !m_pokedFromNeighborSCC.contains(pred);

					if (debugSimulation) {
						getLogger().debug("\t\t\tPoke possible for pred: " + pred);
					}
					if (!pokePossible) {
						// Do not further look at predecessor outside SCC if
						// poke not possible
						continue;
					}
				}

				// If the working vertex has increased its progress
				// measure from the perspective of the predecessor and
				// its priority
				if (decreaseVector(pred.getPriority(), workingVertex.getPM(scc, m_GlobalInfinity), localInfinity) > pred
						.getBEff()) {

					// A Duplicator vertex is only interested in an increased
					// progress measure if the working vertex was its
					// best choice previously and it has no better
					// alternative now
					if (pred.isDuplicatorVertex()
							&& (decreaseVector(pred.getPriority(), oldProgressMeasure, localInfinity) == pred.getBEff()
									|| (pokePossible && pred.getBEff() == 0))) {

						// If trying to use a vertex outside of the SCC make
						// sure the neighbor counter was initialized
						// before accessing it
						if (pokePossible) {
							if (pred.getC() == 0) {
								int oldPredC = pred.getC();
								pred.setC(m_Game.getSuccessors(pred).size());
								saveCChange(pred, oldPredC, m_CurrentChanges);
							}
						}

						if (pred.getC() == 1) {
							// It has no better alternative,
							// adding to working list or poking
							if (pokePossible) {
								m_pokedFromNeighborSCC.add(pred);

								if (debugSimulation) {
									getLogger().debug("\t\t\tPred has no better alternative, poking.");
								}
							} else {
								addVertexToWorkingList(pred);

								if (debugSimulation) {
									getLogger().debug("\t\t\tPred has no better alternative, adding.");
								}
							}
						} else if (pred.getC() > 1) {
							// It has a better alternative, reducing number of
							// neighbors that represent the best choice for the
							// predecessor
							int oldPredC = pred.getC();
							pred.setC(pred.getC() - 1);
							saveCChange(pred, oldPredC, m_CurrentChanges);

							if (debugSimulation) {
								getLogger().debug("\t\t\tPred has a better alternative.");
							}
						}
					} else if (pred.isSpoilerVertex()) {
						// A Spoiler vertex is always interested in an increased
						// progress measure,
						// adding to working list or poking
						if (pokePossible) {
							m_pokedFromNeighborSCC.add(pred);

							if (debugSimulation) {
								getLogger().debug("\t\t\tPred is spoiler, poking.");
							}
						} else {
							addVertexToWorkingList(pred);

							if (debugSimulation) {
								getLogger().debug("\t\t\tPred is spoiler, adding.");
							}
						}
					}
				}
			}

			// Update poked set if worked a poked vertex
			if (isUsingSCCs() && m_pokedFromNeighborSCC.contains(workingVertex)) {
				m_pokedFromNeighborSCC.remove(workingVertex);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in efficientLiftingAlgorithm");
				throw new OperationCanceledException(this.getClass());
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#getGameGraph()
	 */
	@Override
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}
}