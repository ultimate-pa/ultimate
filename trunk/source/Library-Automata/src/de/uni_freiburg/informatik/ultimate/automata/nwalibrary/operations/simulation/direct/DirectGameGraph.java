/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.direct;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;

/**
 * Game graph that realizes <b>direct simulation</b>.<br/>
 * In direct simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must also visit one at his next turn.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 direct simulates
 * q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class DirectGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

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
	 * The state factory used for creating states.
	 */
	private final StateFactory<STATE> m_StateFactory;

	/**
	 * Creates a new direct game graph by using the given buechi automaton.
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
	 *            State factory used for state creation The state factory used
	 *            for creating states.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public DirectGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			final StateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		super(services, progressTimer, logger, stateFactory, buechi);
		INestedWordAutomatonOldApi<LETTER, STATE> preparedBuechi = getAutomaton();
		verifyAutomatonValidity(preparedBuechi);

		m_Services = services;
		m_Buechi = preparedBuechi;
		m_StateFactory = stateFactory;
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
	public INestedWordAutomatonOldApi<LETTER, STATE> generateAutomatonFromGraph() throws AutomataOperationCanceledException {
		SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT);
		}

		// Determine which states to merge
		UnionFind<STATE> uf = new UnionFind<>();
		for (STATE state : m_Buechi.getStates()) {
			uf.makeEquivalenceClass(state);
		}
		HashRelation<STATE, STATE> similarStates = new HashRelation<>();
		for (SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// all the states we need are in V1...
			if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
				STATE state1 = v.getQ0();
				STATE state2 = v.getQ1();
				if (state1 != null && state2 != null) {
					similarStates.addPair(state1, state2);
				}
			}
		}
		// Merge states if they simulate each other
		for (STATE state1 : similarStates.getDomain()) {
			for (STATE state2 : similarStates.getImage(state1)) {
				// Only merge if simulation holds in both directions
				if (similarStates.containsPair(state2, state1)) {
					uf.union(state1, state2);
				}
			}
		}

		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/table filled");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Merge states
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(m_Services,
				m_Buechi.getInternalAlphabet(), null, null, m_StateFactory);
		Set<STATE> representativesOfInitials = new HashSet<>();
		for (STATE initial : m_Buechi.getInitialStates()) {
			representativesOfInitials.add(uf.find(initial));
		}

		int resultAmountOfStates = 0;

		Map<STATE, STATE> input2result = new HashMap<>(m_Buechi.size());
		for (STATE representative : uf.getAllRepresentatives()) {
			boolean isInitial = representativesOfInitials.contains(representative);
			boolean isFinal = m_Buechi.isFinal(representative);
			Set<STATE> eqClass = uf.getEquivalenceClassMembers(representative);
			STATE resultState = m_StateFactory.minimize(eqClass);

			result.addState(isInitial, isFinal, resultState);
			resultAmountOfStates++;

			for (STATE eqClassMember : eqClass) {
				input2result.put(eqClassMember, resultState);
			}
		}

		int resultAmountOfTransitions = 0;

		for (STATE state : uf.getAllRepresentatives()) {
			STATE pred = input2result.get(state);
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Buechi.internalSuccessors(state)) {
				STATE succ = input2result.get(outTrans.getSucc());
				result.addInternalTransition(pred, outTrans.getLetter(), succ);
				resultAmountOfTransitions++;
			}
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

		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/states added to result BA");
			throw new AutomataOperationCanceledException(this.getClass());
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
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		long graphBuildTimeStart = System.currentTimeMillis();

		// Calculate v1 [paper ref 10]
		for (STATE q0 : m_Buechi.getStates()) {
			m_BuechiAmountOfStates++;

			for (STATE q1 : m_Buechi.getStates()) {
				SpoilerVertex<LETTER, STATE> v1e = new SpoilerVertex<>(0, false, q0, q1);
				addSpoilerVertex(v1e);
			}

			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraphFromBuechi/calculating v0 und v1");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (STATE q0 : m_Buechi.getStates()) {
			boolean countedTransitionsForQ0 = false;

			for (STATE q1 : m_Buechi.getStates()) {
				Set<LETTER> relevantLetters = new HashSet<>();
				relevantLetters.addAll(m_Buechi.lettersInternalIncoming(q0));
				relevantLetters.addAll(m_Buechi.lettersInternal(q1));
				for (LETTER s : relevantLetters) {
					DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(0, false, q0, q1, s);
					addDuplicatorVertex(v0e);
					// V1 -> V0 edges [paper ref 11]
					for (STATE pred0 : m_Buechi.predInternal(q0, s)) {
						// Only add edge if duplicator does not directly loose
						if (!m_Buechi.isFinal(pred0) || m_Buechi.isFinal(q1)) {
							addEdge(getSpoilerVertex(pred0, q1, false), v0e);
							m_GraphAmountOfEdges++;
						}

						// Make sure to only count this transitions one time for
						// q0
						if (!countedTransitionsForQ0) {
							m_BuechiAmountOfTransitions++;
						}
					}

					// V0 -> V1 edges [paper ref 11]
					for (STATE succ1 : m_Buechi.succInternal(q1, s)) {
						// Only add edge if duplicator does not directly loose
						if (!m_Buechi.isFinal(q0) || m_Buechi.isFinal(succ1)) {
							addEdge(v0e, getSpoilerVertex(q0, succ1, false));
							m_GraphAmountOfEdges++;
						}
					}
				}
				countedTransitionsForQ0 = true;
			}

			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraphFromBuechi/calculating v0 und v1");
				throw new AutomataOperationCanceledException(this.getClass());
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

		setGraphBuildTime(System.currentTimeMillis() - graphBuildTimeStart);
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
