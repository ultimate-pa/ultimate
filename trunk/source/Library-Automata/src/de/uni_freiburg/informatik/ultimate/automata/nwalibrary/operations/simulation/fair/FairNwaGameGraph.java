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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.SpoilerDoubleDeckerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap6;
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
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(State of spoiler or q0, Letter spoiler used before, State of
	 * duplicator or q1, bit, type of transition, hierPred)</b>.
	 */
	private final NestedMap6<STATE, STATE, LETTER, Boolean, TransitionType, STATE, DuplicatorVertex<LETTER, STATE>> m_BuechiStatesToGraphDuplicatorVertex;

	/**
	 * The underlying nwa automaton, as double decker automaton, from which the
	 * game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_Nwa;

	public FairNwaGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final Logger logger, final INestedWordAutomatonOldApi<LETTER, STATE> nwa,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, progressTimer, logger, nwa, stateFactory);
		// TODO Do we have a better conversion method? One that can not alter
		// the automaton itself because this might influence simulation metrics.

		// To derive down states of automaton ensure it
		// is a double decker automaton
		m_Nwa = new RemoveUnreachable<LETTER, STATE>(services, nwa).getResult();
		m_BuechiStatesToGraphDuplicatorVertex = new NestedMap6<>();
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

		// Generate vertices
		for (STATE leftState : m_Nwa.getStates()) {
			increaseBuechiAmountOfStates();

			for (STATE rightState : m_Nwa.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				SpoilerDoubleDeckerVertex<LETTER, STATE> spoilerVertex = new SpoilerDoubleDeckerVertex<>(priority,
						false, leftState, rightState);
				applyVertexDownStatesToVertex(spoilerVertex);
				addSpoilerVertex(spoilerVertex);

				// Generate Duplicator vertices (leftState, rightState, letter)
				// Vertices generated by internal transitions
				for (LETTER letter : m_Nwa.lettersInternalIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(2,
							false, leftState, rightState, letter, TransitionType.INTERNAL);
					applyVertexDownStatesToVertex(duplicatorVertex);
					addDuplicatorVertex(duplicatorVertex);
				}
				// Vertices generated by call transitions
				for (LETTER letter : m_Nwa.lettersCallIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(2,
							false, leftState, rightState, letter, TransitionType.CALL);
					applyVertexDownStatesToVertex(duplicatorVertex);
					addDuplicatorVertex(duplicatorVertex);
				}
				// Vertices generated by return transitions
				for (IncomingReturnTransition<LETTER, STATE> transition : m_Nwa.returnPredecessors(leftState)) {
					// Only create vertex if the return transition is
					// possible to go from here.
					// That is when in (q0, q1) -> (q2, q1, r/q3),
					// q0 has q3 as down state
					if (hasDownState(transition.getLinPred(), transition.getHierPred())) {
						DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
								2, false, leftState, rightState, transition.getLetter(), TransitionType.RETURN,
								transition.getHierPred());
						applyVertexDownStatesToVertex(duplicatorVertex);
						addDuplicatorVertex(duplicatorVertex);
					}
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

		// Generate edges
		for (STATE edgeDest : m_Nwa.getStates()) {
			// Edges generated by internal transitions
			for (IncomingInternalTransition<LETTER, STATE> trans : m_Nwa.internalPredecessors(edgeDest)) {
				increaseBuechiAmountOfTransitions();

				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							TransitionType.INTERNAL, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.INTERNAL,
							null);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating internal edges");
						throw new OperationCanceledException(this.getClass());
					}
				}

				getBuechiTransitions().add(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}

			// Edges generated by call transitions
			for (IncomingCallTransition<LETTER, STATE> trans : m_Nwa.callPredecessors(edgeDest)) {
				increaseBuechiAmountOfTransitions();

				// Calling should be possible regardless of the stack
				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -c-> q2 : (x, q1, c) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							TransitionType.CALL, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -c-> q2 : (q1, x) -> (q2, x, c)
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.CALL, null);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating call edges");
						throw new OperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}

			// Edges generated by return transitions
			for (IncomingReturnTransition<LETTER, STATE> trans : m_Nwa.returnPredecessors(edgeDest)) {
				increaseBuechiAmountOfTransitions();

				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -r/q0-> q2 : (x, q1, r/q0) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getLinPred(), trans.getLetter(),
							false, TransitionType.RETURN, trans.getHierPred());
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					// Ensured that the edge represents a possible move.
					// This is when the hierPred state is a down state of q1
					boolean isEdgePossible = hasDownState(trans.getLinPred(), trans.getHierPred());
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -r/q0-> q2 : (q1, x) -> (q2, x, r/q0)
					src = getSpoilerVertex(trans.getLinPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.RETURN,
							trans.getHierPred());
					// Ensured that the edge represents a possible move.
					// This is when the hierPred state is a down state of q1
					isEdgePossible = hasDownState(trans.getLinPred(), trans.getHierPred());
					if (src != null && dest != null && isEdgePossible) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating return edges");
						throw new OperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}
		}

		// TODO Generate summarize edges
		// TODO Ensure that no illegal vertex-down-states where generated. They
		// lead to edges between vertices that represent illegal moves.

		setGraphBuildTime(System.currentTimeMillis() - graphBuildTimeStart);
	}

	/**
	 * Unsupported operation. Use
	 * {@link #getDuplicatorVertex(Object, Object, Object, boolean, TransitionType, Object)}
	 * instead.
	 * 
	 * @throws UnsupportedOperationException
	 *             Operation is not supported.
	 */
	@Override
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit) {
		throw new UnsupportedOperationException(
				"Use getDuplicatorVertex(q0, q1, a, bit, transType, hierPred) instead.");
	}

	/**
	 * Gets a Duplicator vertex by its signature. See
	 * {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 * 
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param a
	 *            Used letter
	 * @param bit
	 *            Extra bit of the vertex
	 * @param transType
	 *            Type of the transition
	 * @param hierPred
	 *            hierPred if the transition is of type
	 *            {@link TransitionType#RETURN} or <tt>null</tt> instead.
	 * @return The duplicator vertex associated to the given signature. See
	 *         {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit, final TransitionType transType, final STATE hierPred) {
		return m_BuechiStatesToGraphDuplicatorVertex.get(q0, q1, a, bit, transType, hierPred);
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
	 */
	private void applyVertexDownStatesToVertex(final DuplicatorDoubleDeckerVertex<LETTER, STATE> vertex) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1());
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
	 */
	private void applyVertexDownStatesToVertex(final SpoilerDoubleDeckerVertex<LETTER, STATE> vertex) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1());
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
	 * @return Iterator over all possible vertex down states for two given up
	 *         states
	 */
	private Iterator<VertexDownState<STATE>> constructAllVertexDownStates(final STATE leftUpState,
			final STATE rightUpState) {
		Set<STATE> leftDownStates = m_Nwa.getDownStates(leftUpState);
		Set<STATE> rightDownStates = m_Nwa.getDownStates(leftUpState);
		Set<VertexDownState<STATE>> vertexDownStates = new LinkedHashSet<>();
		for (STATE leftDownState : leftDownStates) {
			for (STATE rightDownState : rightDownStates) {
				vertexDownStates.add(new VertexDownState<>(leftDownState, rightDownState));
			}
		}
		return vertexDownStates.iterator();
	}

	/**
	 * Returns if a given up state has a given down state.
	 * 
	 * @param upState
	 *            Up state in question
	 * @param downState
	 *            Down state in question
	 * @return If the given up state has the given down state.
	 */
	private boolean hasDownState(final STATE upState, final STATE downState) {
		return m_Nwa.getDownStates(upState).contains(downState);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#addDuplicatorVertex(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.operations.simulation.vertices.
	 * DuplicatorVertex)
	 */
	@Override
	protected void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		if (vertex instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
			DuplicatorDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) vertex;
			getInternalDuplicatorVerticesField().add(vertexAsDD);
			m_BuechiStatesToGraphDuplicatorVertex.put(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(),
					vertexAsDD.isB(), vertexAsDD.getTransitionType(), vertexAsDD.getHierPred(), vertexAsDD);
		} else {
			super.addDuplicatorVertex(vertex);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#removeDuplicatorVertex(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.operations.simulation.vertices.
	 * DuplicatorVertex)
	 */
	@Override
	protected void removeDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		if (vertex instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
			DuplicatorDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) vertex;
			getInternalDuplicatorVerticesField().remove(vertexAsDD);
			m_BuechiStatesToGraphDuplicatorVertex.put(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(),
					vertexAsDD.isB(), vertexAsDD.getTransitionType(), vertexAsDD.getHierPred(), null);
		} else {
			super.removeDuplicatorVertex(vertex);
		}
	}
}