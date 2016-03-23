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

import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.DuplicatorWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.SpoilerDoubleDeckerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.SummarizeEdge;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.relation.Hep;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.relation.Quin;
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
	 * State symbol that stands for an empty stack.
	 */
	private final STATE m_Bottom;
	/**
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(State of spoiler or q0, Letter spoiler used before, State of
	 * duplicator or q1, bit, type of transition, summarize edge, sink)</b>.
	 */
	private final HashMap<Hep<STATE, STATE, LETTER, Boolean, TransitionType, SummarizeEdge<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>>, DuplicatorVertex<LETTER, STATE>> m_BuechiStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects
	 * by using their representation:<br/>
	 * <b>(State of spoiler or q0, State of duplicator or q1, bit)</b>.
	 */
	private final HashMap<Quin<STATE, STATE, Boolean, SummarizeEdge<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>>, SpoilerVertex<LETTER, STATE>> m_BuechiStatesToGraphSpoilerVertex;
	/**
	 * Data structure of all duplicator vertices that use an outgoing return
	 * transition. They are used for summarize edge generation.
	 */
	private final HashSet<DuplicatorDoubleDeckerVertex<LETTER, STATE>> m_DuplicatorReturningVertices;
	/**
	 * Map of all duplicator winning sinks of the graph. Provides a fast access
	 * via the sink entry.
	 */
	private final HashMap<SpoilerDoubleDeckerVertex<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>> m_EntryToSink;
	/**
	 * The underlying nwa automaton, as double decker automaton, from which the
	 * game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_Nwa;
	/**
	 * Map of all summarize edges of the graph. Provides a fast access via
	 * source and destination of the edge.
	 */
	private final HashMap<Pair<SpoilerDoubleDeckerVertex<LETTER, STATE>, SpoilerDoubleDeckerVertex<LETTER, STATE>>, SummarizeEdge<LETTER, STATE>> m_SrcDestToSummarizeEdges;

	@SuppressWarnings("unchecked")
	public FairNwaGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final Logger logger, final INestedWordAutomatonOldApi<LETTER, STATE> nwa,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, progressTimer, logger, nwa, stateFactory);
		// TODO Do we have a better conversion method? One that can not alter
		// the automaton itself because this might influence simulation metrics.

		// To derive down states of automaton ensure it
		// is a double decker automaton
		if (nwa instanceof IDoubleDeckerAutomaton<?, ?>) {
			m_Nwa = (IDoubleDeckerAutomaton<LETTER, STATE>) nwa;
		} else {
			m_Nwa = new RemoveUnreachable<LETTER, STATE>(services, nwa).getResult();
		}
		m_BuechiStatesToGraphDuplicatorVertex = new HashMap<>();
		m_BuechiStatesToGraphSpoilerVertex = new HashMap<>();
		m_DuplicatorReturningVertices = new HashSet<>();
		m_SrcDestToSummarizeEdges = new HashMap<>();
		m_EntryToSink = new HashMap<>();
		m_Bottom = m_Nwa.getEmptyStackState();
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
		Logger logger = getLogger();

		logger.debug("Generating vertices.");
		generateVertices();
		logger.debug("Generating regular edges.");
		generateRegularEdges();
		logger.debug("Generating summarize edges.");
		generateSummarizeEdges();
		// TODO Calculate priorities of summarize edges

		m_DuplicatorReturningVertices.clear();
		m_EntryToSink.clear();
		m_SrcDestToSummarizeEdges.clear();

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
		// TODO Can later use getDuplicatorVertex(...., null, null) but for now
		// it should throw an Exception for problem detection.
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
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to if the transition is of
	 *            type {@link TransitionType#SUMMARIZE_ENTRY} or
	 *            {@link TransitionType#SUMMARIZE_EXIT}. Use <tt>null</tt> if
	 *            that is not the case.
	 * @param sink
	 *            Sink the vertex belongs to if the transition is of type
	 *            {@link TransitionType#SINK}. Use <tt>null</tt> if that is not
	 *            the case.
	 * @return The duplicator vertex associated to the given signature. See
	 *         {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit, final TransitionType transType, final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final DuplicatorWinningSink<LETTER, STATE> sink) {
		return m_BuechiStatesToGraphDuplicatorVertex.get(new Hep<>(q0, q1, a, bit, transType, summarizeEdge, sink));
	}

	/**
	 * Unsupported operation. Use
	 * {@link #getSpoilerVertex(Object, Object, boolean, SummarizeEdge)}
	 * instead.
	 * 
	 * @throws UnsupportedOperationException
	 *             Operation is not supported.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit) {
		throw new UnsupportedOperationException("Use getSpoilerVertex(q0, q1, a, bit, summarizeEdge) instead.");
		// TODO Can later use getSpoilerVertex(...., null, null) but for now
		// it should throw an Exception for problem detection.
	}

	/**
	 * Gets a Spoiler vertex by its signature. See
	 * {@link #getSpoilerVertex(Object, Object, boolean)}.
	 * 
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param bit
	 *            Extra bit of the vertex
	 * @param transType
	 *            Type of the transition
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to. Use <tt>null</tt> if the
	 *            vertex does not belong to one.
	 * @param sink
	 *            Sink the vertex belongs to. Use <tt>null</tt> if the vertex
	 *            does not belong to one.
	 * @return The spoiler vertex associated to the given signature. See
	 *         {@link #getSpoilerVertex(Object, Object, boolean)}.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit,
			final SummarizeEdge<LETTER, STATE> summarizeEdge, final DuplicatorWinningSink<LETTER, STATE> sink) {
		return m_BuechiStatesToGraphSpoilerVertex.get(new Quin<>(q0, q1, bit, summarizeEdge, sink));
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
		// Do noting to accept nwa automata
	}

	/**
	 * Creates and adds a duplicator winning sink to the given sink entry. To
	 * form a valid edge it creates a pair of two states after the entry. In
	 * detail this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink ->
	 * DuplicatorSink -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 0 to form a winning vertex for
	 * Duplicator.
	 * 
	 * @param sinkEntry
	 *            Entry vertex of the sink
	 */
	private void addDuplicatorWinningSink(final SpoilerDoubleDeckerVertex<LETTER, STATE> sinkEntry) {
		// Only add if not already existent
		if (m_EntryToSink.get(sinkEntry) == null) {
			DuplicatorWinningSink<LETTER, STATE> sink = new DuplicatorWinningSink<>(sinkEntry);
			m_EntryToSink.put(sinkEntry, sink);

			DuplicatorVertex<LETTER, STATE> duplicatorSink = sink.getDuplicatorSink();
			SpoilerVertex<LETTER, STATE> spoilerSink = sink.getSpoilerSink();

			// Add shadow vertices
			addDuplicatorVertex(duplicatorSink);
			addSpoilerVertex(spoilerSink);

			// Add edges connecting the sink
			addEdge(sinkEntry, duplicatorSink);
			addEdge(duplicatorSink, spoilerSink);
			addEdge(spoilerSink, duplicatorSink);
		}
	}

	/**
	 * Creates and adds a summarize edge with given source and destination. To
	 * form a valid edge it creates a pair of three states between source and
	 * destination. In detail this will be: <b>src -> DuplicatorShadowVertex1 ->
	 * SpoilerShadowVertex -> DuplicatorShadowVertex2 -> dest</b>. <br/>
	 * <br/>
	 * The SpoilerShadowVertex will have no priority by default, it must be
	 * taken care of this afterwards.
	 * 
	 * @param src
	 *            Source of the summarize edge
	 * @param dest
	 *            Destination of the summarize edge
	 */
	private void addSummarizeEdge(final SpoilerDoubleDeckerVertex<LETTER, STATE> src,
			final SpoilerDoubleDeckerVertex<LETTER, STATE> dest) {
		// Only add if not already existent
		if (m_SrcDestToSummarizeEdges.get(new Pair<>(src, dest)) == null) {
			SummarizeEdge<LETTER, STATE> summarizeEdge = new SummarizeEdge<>(src, dest);
			m_SrcDestToSummarizeEdges.put(new Pair<>(src, dest), summarizeEdge);

			DuplicatorVertex<LETTER, STATE> entryShadowVertex = summarizeEdge.getEntryShadowVertex();
			SpoilerVertex<LETTER, STATE> middleShadowVertex = summarizeEdge.getMiddleShadowVertex();
			DuplicatorVertex<LETTER, STATE> exitShadowVertex = summarizeEdge.getExitShadowVertex();

			// Add shadow vertices
			addDuplicatorVertex(entryShadowVertex);
			addSpoilerVertex(middleShadowVertex);
			addDuplicatorVertex(exitShadowVertex);

			// Add edges connecting source and destination with shadow vertices
			addEdge(summarizeEdge.getSource(), entryShadowVertex);
			addEdge(entryShadowVertex, middleShadowVertex);
			addEdge(middleShadowVertex, exitShadowVertex);
			addEdge(exitShadowVertex, summarizeEdge.getDestination());
		}
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
	 * Generates the regular edges of the game graph from the input automaton.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void generateRegularEdges() throws OperationCanceledException {
		for (STATE edgeDest : m_Nwa.getStates()) {
			// Edges generated by internal transitions
			for (IncomingInternalTransition<LETTER, STATE> trans : m_Nwa.internalPredecessors(edgeDest)) {
				increaseBuechiAmountOfTransitions();

				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							TransitionType.INTERNAL, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.INTERNAL,
							null, null);
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

				// Calling is possible regardless of the stack
				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -c-> q2 : (x, q1, c) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							TransitionType.CALL, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();
					}

					// Spoiler edges q1 -c-> q2 : (q1, x) -> (q2, x, c)
					src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.CALL, null,
							null);
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
							false, TransitionType.RETURN, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					// Ensure that the edge represents a possible move.
					// This is when the hierPred state is a down state of q1
					boolean isEdgePossible = hasDownState(trans.getLinPred(), trans.getHierPred());
					if (src != null && dest != null) {
						addEdge(src, dest);
						increaseGraphAmountOfEdges();

						// Remember vertex since we need it later for summarize
						// edge generation
						if (src instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
							m_DuplicatorReturningVertices.add((DuplicatorDoubleDeckerVertex<LETTER, STATE>) src);
						}
					}

					// Spoiler edges q1 -r/q0-> q2 : (q1, x) -> (q2, x, r/q0)
					src = getSpoilerVertex(trans.getLinPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, TransitionType.RETURN,
							null, null);
					// Ensure that the edge represents a possible move.
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
	}

	/**
	 * Generates the summarize edges of the game graph from the input automaton.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void generateSummarizeEdges() throws OperationCanceledException {
		// Return edges (q', q1 [q5, q6]) -> (q0, q1, r/q2) -> (q0, q3) lead
		// to creation of summarize edge (q5, q6) -> (q0, q3)
		for (DuplicatorDoubleDeckerVertex<LETTER, STATE> returnInvoker : m_DuplicatorReturningVertices) {
			for (Vertex<LETTER, STATE> summarizeDest : getSuccessors(returnInvoker)) {
				if (!(summarizeDest instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
					continue;
				}
				SpoilerDoubleDeckerVertex<LETTER, STATE> summarizeDestAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) summarizeDest;
				for (Vertex<LETTER, STATE> preInvoker : getPredecessors(returnInvoker)) {
					if (!(preInvoker instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
						continue;
					}
					SpoilerDoubleDeckerVertex<LETTER, STATE> preInvokerAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) preInvoker;
					for (VertexDownState<STATE> vertexDownState : preInvokerAsDD.getVertexDownStates()) {
						// If vertex down state [q, q'] does not contain
						// bottom then use the corresponding vertex as source
						// of the summarize edge
						STATE leftDownState = vertexDownState.getLeftDownState();
						STATE rightDownState = vertexDownState.getRightDownState();
						if (leftDownState.equals(m_Bottom) || rightDownState.equals(m_Bottom)) {
							continue;
						}
						SpoilerVertex<LETTER, STATE> summarizeSrc = getSpoilerVertex(leftDownState, rightDownState,
								false, null, null);
						if (summarizeSrc == null || !(summarizeSrc instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
							continue;
						}
						SpoilerDoubleDeckerVertex<LETTER, STATE> summarizeSrcAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) summarizeSrc;
						addSummarizeEdge(summarizeSrcAsDD, summarizeDestAsDD);
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraphFromBuechi/generating summarize edges");
					throw new OperationCanceledException(this.getClass());
				}
			}
		}

		// Delete all incoming and outgoing edges of the invoker since they are
		// covered by summarize edges
		for (DuplicatorDoubleDeckerVertex<LETTER, STATE> returnInvoker : m_DuplicatorReturningVertices) {
			for (Vertex<LETTER, STATE> succ : getSuccessors(returnInvoker)) {
				removeEdge(returnInvoker, succ);
			}
			for (Vertex<LETTER, STATE> pre : getPredecessors(returnInvoker)) {
				removeEdge(pre, returnInvoker);
				// Care for dead end spoiler vertices because they are not
				// allowed in a legal game graph.
				// They need to form a legal instant win for Duplicator.
				if (!hasSuccessors(pre) && pre instanceof SpoilerDoubleDeckerVertex<?, ?>) {
					SpoilerDoubleDeckerVertex<LETTER, STATE> preAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) pre;
					addDuplicatorWinningSink(preAsDD);
				}
			}
			// Remove not reachable vertex
			removeDuplicatorVertex(returnInvoker);
		}
	}

	/**
	 * Generates the vertices of the game graph from the input automaton.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void generateVertices() throws OperationCanceledException {
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
						// Only add if not already existent
						if (getDuplicatorVertex(leftState, rightState, transition.getLetter(), false,
								TransitionType.RETURN, null, null) == null) {
							DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
									2, false, leftState, rightState, transition.getLetter(), TransitionType.RETURN);
							applyVertexDownStatesToVertex(duplicatorVertex);
							addDuplicatorVertex(duplicatorVertex);
						}
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
			m_BuechiStatesToGraphDuplicatorVertex.put(
					new Hep<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(), vertexAsDD.isB(),
							vertexAsDD.getTransitionType(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()),
					vertexAsDD);
		} else {
			super.addDuplicatorVertex(vertex);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#addSpoilerVertex(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.operations.simulation.vertices.
	 * SpoilerVertex)
	 */
	@Override
	protected void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		if (vertex instanceof SpoilerDoubleDeckerVertex<?, ?>) {
			SpoilerDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) vertex;
			getInternalSpoilerVerticesField().add(vertexAsDD);
			m_BuechiStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.isB(),
					vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), vertexAsDD);
		} else {
			super.addSpoilerVertex(vertex);
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
			m_BuechiStatesToGraphDuplicatorVertex
					.put(new Hep<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(), vertexAsDD.isB(),
							vertexAsDD.getTransitionType(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), null);
		} else {
			super.removeDuplicatorVertex(vertex);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#removeSpoilerVertex(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.operations.simulation.vertices.
	 * SpoilerVertex)
	 */
	@Override
	protected void removeSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		if (vertex instanceof SpoilerDoubleDeckerVertex<?, ?>) {
			SpoilerDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) vertex;
			getInternalSpoilerVerticesField().remove(vertexAsDD);
			m_BuechiStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.isB(),
					vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), null);
		} else {
			super.removeSpoilerVertex(vertex);
		}
	}
}