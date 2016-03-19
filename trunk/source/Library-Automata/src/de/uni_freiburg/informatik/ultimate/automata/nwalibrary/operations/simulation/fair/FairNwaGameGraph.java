/*
 * Copyright (C) 2015-2016 Daniel Tischner
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.VertexDownState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.DuplicatorDoubleDeckerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.SpoilerDoubleDeckerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Game graph that realizes <b>fair simulation</b> for NWA automata.<br/>
 * In fair simulation each time <i>Spoiler</i> builds an accepting word
 * <i>Duplicator</i>s word must also be accepting.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 fair simulates
 * q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class FairNwaGameGraph<LETTER, STATE> extends FairGameGraph<LETTER, STATE> {

	/**
	 * The underlying nwa automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Nwa;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;

	public FairNwaGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final Logger logger, final INestedWordAutomatonOldApi<LETTER, STATE> nwa,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, progressTimer, logger, nwa, stateFactory);
		m_Nwa = nwa;
		m_Services = services;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	public void generateGameGraphFromBuechi() throws OperationCanceledException {
		long graphBuildTimeStart = System.currentTimeMillis();

		// TODO Do we have a better conversion method? One that can not alter
		// the automaton itself because this might influence simulation metrics.

		// To derive down states of automaton ensure it
		// is a double decker automaton
		IDoubleDeckerAutomaton<LETTER, STATE> nwa = new RemoveUnreachable<LETTER, STATE>(m_Services, m_Nwa).getResult();

		// Generate vertices
		for (STATE leftState : nwa.getStates()) {
			increaseBuechiAmountOfStates();

			for (STATE rightState : nwa.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				SpoilerDoubleDeckerVertex<LETTER, STATE> spoilerVertex = new SpoilerDoubleDeckerVertex<>(priority,
						false, leftState, rightState);
				applyVertexDownStatesToVertex(spoilerVertex, nwa);
				addSpoilerVertex(spoilerVertex);

				// Generate Duplicator vertices (leftState, rightState, letter)
				for (LETTER letter : nwa.lettersInternalIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(2,
							false, leftState, rightState, letter, TransitionType.INTERNAL);
					applyVertexDownStatesToVertex(duplicatorVertex, nwa);
					addDuplicatorVertex(duplicatorVertex);
				}
				for (LETTER letter : nwa.lettersCallIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(2,
							false, leftState, rightState, letter, TransitionType.CALL);
					applyVertexDownStatesToVertex(duplicatorVertex, nwa);
					addDuplicatorVertex(duplicatorVertex);
				}
				for (IncomingReturnTransition<LETTER, STATE> transition : nwa.returnPredecessors(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(2,
							false, leftState, rightState, transition.getLetter(), TransitionType.RETURN);
					duplicatorVertex.setHierPred(transition.getHierPred());
					applyVertexDownStatesToVertex(duplicatorVertex, nwa);
					addDuplicatorVertex(duplicatorVertex);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraphFromBuechi/generating vertices");
					throw new OperationCanceledException(this.getClass());
				}
			}

			// Generate an equivalence class for every state from
			// the nwa automaton
			getEquivalenceClasses().makeEquivalenceClass(leftState);
		}

		increaseGlobalInfinity();

		// TODO Overhaul this for the use with NWA,
		// also generate summarize-edges

		// Generate edges
		for (STATE edgeDest : nwa.getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> trans : nwa.internalPredecessors(edgeDest)) {
				increaseBuechiAmountOfTransitions();

				for (STATE fixState : nwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(),
							false);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating edges");
						throw new OperationCanceledException(this.getClass());
					}
				}

				getBuechiTransitions().add(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}
		}

		setGraphBuildTime(System.currentTimeMillis() - graphBuildTimeStart);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#verifyAutomatonValidity(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.INestedWordAutomatonOldApi)
	 */
	@Override
	public void verifyAutomatonValidity(final INestedWordAutomatonOldApi<LETTER, STATE> automaton) {
		// Accept nwa automata
	}

	/**
	 * Applies all possible down state configurations to a given vertex that
	 * specifies the up states.
	 * 
	 * @param vertex
	 *            Vertex to add configurations to
	 * @param doubleDeckerAutomaton
	 *            DoubleDecker automaton that holds the down state information
	 *            of the used up states
	 */
	private void applyVertexDownStatesToVertex(final DuplicatorDoubleDeckerVertex<LETTER, STATE> vertex,
			final IDoubleDeckerAutomaton<LETTER, STATE> doubleDeckerAutomaton) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1(), doubleDeckerAutomaton);
		while (vertexDownStatesIter.hasNext()) {
			vertex.addVertexDownState(vertexDownStatesIter.next());
		}
	}

	/**
	 * Applies all possible down state configurations to a given vertex that
	 * specifies the up states.
	 * 
	 * @param vertex
	 *            Vertex to add configurations to
	 * @param doubleDeckerAutomaton
	 *            DoubleDecker automaton that holds the down state information
	 *            of the used up states
	 */
	private void applyVertexDownStatesToVertex(final SpoilerDoubleDeckerVertex<LETTER, STATE> vertex,
			final IDoubleDeckerAutomaton<LETTER, STATE> doubleDeckerAutomaton) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1(), doubleDeckerAutomaton);
		while (vertexDownStatesIter.hasNext()) {
			vertex.addVertexDownState(vertexDownStatesIter.next());
		}
	}

	/**
	 * Creates an iterator over all possible vertex down states for two given up
	 * states.
	 * 
	 * @param leftUpState
	 *            The left up state to combine its down states
	 * @param rightUpState
	 *            The right up state to combine its down states
	 * @param doubleDeckerAutomaton
	 *            DoubleDecker automaton that holds the down state information
	 *            of the used up states
	 * @return Iterator over all possible vertex down states for two given up
	 *         states
	 */
	private Iterator<VertexDownState<STATE>> constructAllVertexDownStates(final STATE leftUpState,
			final STATE rightUpState, final IDoubleDeckerAutomaton<LETTER, STATE> doubleDeckerAutomaton) {
		Set<STATE> leftDownStates = doubleDeckerAutomaton.getDownStates(leftUpState);
		Set<STATE> rightDownStates = doubleDeckerAutomaton.getDownStates(leftUpState);
		Set<VertexDownState<STATE>> vertexDownStates = new LinkedHashSet<>();
		for (STATE leftDownState : leftDownStates) {
			for (STATE rightDownState : rightDownStates) {
				vertexDownStates.add(new VertexDownState<>(leftDownState, rightDownState));
			}
		}
		return vertexDownStates.iterator();
	}
}