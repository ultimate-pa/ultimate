/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.delayed;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Game graph that realizes <b>delayed simulation</b>.<br/>
 * In delayed simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must at least visit one in the future for coverage.<br/>
 * To reflect <i>Duplicator</i>s coverage the delayed game graph uses vertices
 * that have an extra bit.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 delayed
 * simulates q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 *
 * The implementation is based on the following paper. Kousha Etessami, Thomas
 * Wilke, Rebecca A. Schuller: Fair Simulation Relations, Parity Games, and
 * State Space Reduction for Bu"chi Automata. SIAM J. Comput. 34(5): 1159-1175
 * (2005)
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class DelayedGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	/**
	 * Amount of states the inputed buechi automata has.
	 */
	private int m_BuechiAmountOfStates;
	/**
	 * Amount of transitions the inputed buechi automata has.
	 */
	private int m_BuechiAmountOfTransitions;
	/**
	 * Amount of edges the game graph has.
	 */
	private int m_GraphAmountOfEdges;
	/**
	 * Time duration building the graph took in milliseconds.
	 */
	private long m_GraphBuildTime;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;

	/**
	 * Creates a new delayed game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @param stateFactory
	 *            State factory used for state creation
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public DelayedGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, progressTimer, logger, stateFactory, buechi);
		INestedWordAutomatonOldApi<LETTER, STATE> preparedBuechi = getAutomaton();
		verifyAutomatonValidity(preparedBuechi);

		m_Services = services;
		m_Buechi = preparedBuechi;
		m_BuechiAmountOfStates = 0;
		m_BuechiAmountOfTransitions = 0;
		m_GraphBuildTime = 0;
		m_GraphAmountOfEdges = 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> generateAutomatonFromGraph() throws OperationCanceledException {
		SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT);
		}

		// Determine which states to merge
		ArrayList<STATE> states = new ArrayList<>();
		states.addAll(m_Buechi.getStates());
		boolean[][] table = new boolean[states.size()][states.size()];
		for (SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// All the states we need are in spoiler vertices

			// Which node do we have to consider in order to obtain the
			// simulation information for the state pair (q0,q1) ?
			// According to Lemma 4 (page 1166) of the above mentioned paper
			// We consider (q0, q1, true) if q0 is final and q1 is not final
			// and we consider (q0, q1, false) if q0 is not final or q1 is
			// final.
			final boolean considerVertex;
			if (v.isB()) {
				considerVertex = m_Buechi.isFinal(v.getQ0()) && !m_Buechi.isFinal(v.getQ0());
			} else {
				considerVertex = !m_Buechi.isFinal(v.getQ0()) || m_Buechi.isFinal(v.getQ0());
			}

			final boolean skip = (m_Buechi.isFinal(v.getQ0())
					&& (m_Buechi.isFinal(v.getQ1()) ^ m_Buechi.isFinal(v.getQ0()) ^ v.isB()));
			{
				// 2016-05-03 Matthias: I had some doubts about operator
				// precedence
				// added assert, remove if tested well enough.
				boolean skipOld = (m_Buechi.isFinal(v.getQ0()) && m_Buechi.isFinal(v.getQ1())) ^ v.isB()
						^ m_Buechi.isFinal(v.getQ0());
				assert skipOld == skip : "unexpected operator precedence";
			}
			assert considerVertex != skip : "old implementation incorrect";

			if (considerVertex) {
				if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
					table[states.indexOf(v.getQ0())][states.indexOf(v.getQ1())] = true;
				}
			}
		}

		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomaton/table filled");
			throw new OperationCanceledException(this.getClass());
		}

		// Merge states
		boolean[] marker = new boolean[states.size()];
		Set<STATE> temp = new HashSet<>();
		HashMap<STATE, STATE> oldSNames2newSNames = new HashMap<>();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(m_Services,
				m_Buechi.getInternalAlphabet(), null, null, getStateFactory());

		int resultAmountOfStates = 0;

		for (int i = 0; i < states.size(); i++) {
			if (marker[i])
				continue;
			temp.clear();
			temp.add(states.get(i));
			marker[i] = true;
			boolean isFinal = m_Buechi.isFinal(states.get(i));
			boolean isInitial = m_Buechi.isInitial(states.get(i));
			for (int j = i; j < states.size(); j++) {
				if (table[i][j] && table[j][i] && !marker[j]) {
					temp.add(states.get(j));
					marker[j] = true;
					if (m_Buechi.isFinal(states.get(j)))
						isFinal = true;
					if (m_Buechi.isInitial(states.get(j)))
						isInitial = true;
				}
			}
			STATE minimizedStateName = getStateFactory().minimize(temp);
			for (STATE c : temp)
				oldSNames2newSNames.put(c, minimizedStateName);
			result.addState(isInitial, isFinal, minimizedStateName);
			resultAmountOfStates++;
			marker[i] = true;
		}

		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomaton/states added to result BA");
			throw new OperationCanceledException(this.getClass());
		}

		// Add edges
		int resultAmountOfTransitions = 0;

		for (STATE c : m_Buechi.getStates())
			for (LETTER s : m_Buechi.getInternalAlphabet())
				for (STATE succ : m_Buechi.succInternal(c, s)) {
					STATE newPred = oldSNames2newSNames.get(c);
					STATE newSucc = oldSNames2newSNames.get(succ);
					result.addInternalTransition(newPred, s, newSucc);
					resultAmountOfTransitions++;
				}

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(ETimeMeasure.BUILD_RESULT);
			performance.addTimeMeasureValue(ETimeMeasure.BUILD_GRAPH, m_GraphBuildTime);
			performance.setCountingMeasure(ECountingMeasure.REMOVED_STATES,
					m_BuechiAmountOfStates - resultAmountOfStates);
			performance.setCountingMeasure(ECountingMeasure.REMOVED_TRANSITIONS,
					m_BuechiAmountOfTransitions - resultAmountOfTransitions);
			performance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS, m_BuechiAmountOfTransitions);
			performance.setCountingMeasure(ECountingMeasure.BUCHI_STATES, m_BuechiAmountOfStates);
			performance.setCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES, m_GraphAmountOfEdges);
		}

		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	public void generateGameGraphFromAutomaton() throws OperationCanceledException {
		long graphBuildTimeStart = System.currentTimeMillis();

		// Calculate v1 [paper ref 10]
		for (STATE q0 : m_Buechi.getStates()) {
			m_BuechiAmountOfStates++;

			for (STATE q1 : m_Buechi.getStates()) {
				SpoilerVertex<LETTER, STATE> v1e = new SpoilerVertex<>(0, false, q0, q1);
				addSpoilerVertex(v1e);
				if (!m_Buechi.isFinal(q1)) {
					v1e = new SpoilerVertex<>(1, true, q0, q1);
					addSpoilerVertex(v1e);
					increaseGlobalInfinity();
				}
			}
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraph/calculating v0 und v1");
				throw new OperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (STATE q0 : m_Buechi.getStates()) {
			boolean countedTransitionsForQ0 = false;

			for (STATE q1 : m_Buechi.getStates()) {
				for (LETTER s : m_Buechi.lettersInternalIncoming(q0)) {
					if (m_Buechi.predInternal(q0, s).iterator().hasNext()) {
						DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(2, false, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (STATE q2 : m_Buechi.succInternal(q1, s)) {
							addEdge(v0e, getSpoilerVertex(q0, q2, false));
							m_GraphAmountOfEdges++;
						}
						// V1 -> V0 edges [paper ref 11]
						for (STATE q2 : m_Buechi.predInternal(q0, s)) {
							if (!m_Buechi.isFinal(q0)) {
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
								m_GraphAmountOfEdges++;
							}
						}
						v0e = new DuplicatorVertex<>(2, true, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (STATE q2 : m_Buechi.succInternal(q1, s)) {
							if (!m_Buechi.isFinal(q2) && getAmountOfBitsForSpoilerVertices(q0, q2) > 1) {
								addEdge(v0e, getSpoilerVertex(q0, q2, true));
								m_GraphAmountOfEdges++;
							} else {
								addEdge(v0e, getSpoilerVertex(q0, q2, false));
								m_GraphAmountOfEdges++;
							}
						}
						// V1 -> V0 edges [paper ref 11]
						for (STATE q2 : m_Buechi.predInternal(q0, s)) {
							if (getAmountOfBitsForSpoilerVertices(q2, q1) > 1) {
								addEdge(getSpoilerVertex(q2, q1, true), v0e);
								m_GraphAmountOfEdges++;
							}
							if (m_Buechi.isFinal(q0)) {
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
								m_GraphAmountOfEdges++;
							}

							// Make sure to only count this transitions one time
							// for q0
							if (!countedTransitionsForQ0) {
								m_BuechiAmountOfTransitions++;
							}
						}
					}
				}
				countedTransitionsForQ0 = true;
			}
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraph/calculating v0 und v1");
				throw new OperationCanceledException(this.getClass());
			}
		}
		// global infinity = (# of pr==1 nodes) + 1
		increaseGlobalInfinity();
		ILogger logger = getLogger();
		if (logger.isDebugEnabled()) {
			logger.debug("Infinity is " + getGlobalInfinity());
			logger.debug("Number of vertices in game graph: "
					+ (getDuplicatorVertices().size() + getSpoilerVertices().size()));
			logger.debug("Number of vertices in v0: " + getDuplicatorVertices().size());
			logger.debug("Number of vertices in v1: " + getSpoilerVertices().size());
			logger.debug("Number of edges in game graph: " + m_GraphAmountOfEdges);
		}

		m_GraphBuildTime = System.currentTimeMillis() - graphBuildTimeStart;
	}

	/**
	 * Gets the amount of {@link SpoilerVertex} objects that exist in the game
	 * graph with representation (q0, q1). Since there can be such vertices with
	 * the extra bit false and true the returned value is between zero and two.
	 * 
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 * @return The amount of {@link SpoilerVertex} objects that exist in the
	 *         game graph with representation (q0, q1). Since there can be such
	 *         vertices with the extra bit false and true the returned value is
	 *         between zero and two.
	 */
	private int getAmountOfBitsForSpoilerVertices(final STATE q0, final STATE q1) {
		int amount = 0;

		if (getSpoilerVertex(q0, q1, false) != null) {
			amount++;
		}

		if (getSpoilerVertex(q0, q1, true) != null) {
			amount++;
		}

		return amount;
	}

	/**
	 * Sets the internal counter of the amount of buechi states.
	 * 
	 * @param amount
	 *            Amount of buechi states.
	 */
	protected void setBuechiAmountOfStates(final int amount) {
		m_BuechiAmountOfStates = amount;
	}

	/**
	 * Sets the internal counter of the amount of buechi transitions.
	 * 
	 * @param amount
	 *            Amount of buechi transitions.
	 */
	protected void setBuechiAmountOfTransitions(final int amount) {
		m_BuechiAmountOfTransitions = amount;
	}

	/**
	 * Sets the internal counter of the amount of graph edges.
	 * 
	 * @param amount
	 *            Amount of graph edges.
	 */
	protected void setGraphAmountOfEdges(final int amount) {
		m_GraphAmountOfEdges = amount;
	}

	/**
	 * Sets the internal field of the graphBuildTime.
	 * 
	 * @param graphBuildTime
	 *            The graphBuildTime to set
	 */
	protected void setGraphBuildTime(final long graphBuildTime) {
		m_GraphBuildTime = graphBuildTime;
	}
}
