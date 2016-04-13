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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;

/**
 * Breadth-first search that computes the priority of a given summarize edge
 * based on the priorities of vertices in the game graph. The search may pause
 * when reaching a vertex whose priority is not yet known. The search can be
 * resumed when this priority was set. If {@link #isFinished()} returns
 * <tt>true</tt>, the search has finished and the priority for the summarize
 * edge can be get using {@link #getPriorityResult()}.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SummarizeEdgePrioritySearch<LETTER, STATE> {
	/**
	 * Game graph to work on.
	 */
	private final AGameGraph<LETTER, STATE> m_GameGraph;
	/**
	 * If the search has finished. If that is the case then
	 * {@link #getPriorityResult()} returns a valid priority for the summarize
	 * edge.
	 */
	private boolean m_IsFinished;
	/**
	 * Logger to use for logging.
	 */
	private final Logger m_Logger;
	/**
	 * The resulting priority for the summarize edge or
	 * {@link SummarizeEdge#NO_PRIORITY NO_PRIORITY} if unknown.
	 */
	private int m_PriorityResult;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer m_ProgressTimer;
	/**
	 * Queue of vertices to process for the breadth-first search.
	 */
	private final Queue<Vertex<LETTER, STATE>> m_SearchQueue;
	/**
	 * Summarize edge to search priority for.
	 */
	private final SummarizeEdge<LETTER, STATE> m_SummarizeEdge;
	/**
	 * The vertex of this summary edge which has no priority. The search tries
	 * to compute a priority for this vertex.
	 */
	private final Vertex<LETTER, STATE> m_SummarizeEdgeNoPriorityVertex;
	/**
	 * The entry vertex of this summary edge.
	 */
	private final Vertex<LETTER, STATE> m_SummarizeEdgeEntry;
	/**
	 * The exit vertex of this summary edge.
	 */
	private final Vertex<LETTER, STATE> m_SummarizeEdgeExit;
	/**
	 * Data structure that stores for each vertex of the breadth-first search a
	 * search priority value.
	 */
	private final HashMap<Vertex<LETTER, STATE>, Integer> m_VertexToSearchPriority;

	/**
	 * Creates a new summarize edge priority search instance that computes the
	 * priority for the given edge. The search can be started using
	 * {@link #search()}. A search can get stuck if other priorities are not
	 * set, it can be continued by calling {@link #search()} again. The search
	 * has finished when {@link #isFinished()} returns <tt>true</tt>. After that
	 * the resulting priority can be accessed using
	 * {@link #getPriorityResult()}.
	 * 
	 * @param summarizeEdge
	 *            Edge to compute priority for
	 * @param gameGraph
	 *            Game graph to work on
	 * @param logger
	 *            Logger to use for logging
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation
	 */
	public SummarizeEdgePrioritySearch(final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final AGameGraph<LETTER, STATE> gameGraph, final Logger logger, final IProgressAwareTimer progressTimer) {
		m_Logger = logger;
		m_ProgressTimer = progressTimer;
		m_SummarizeEdge = summarizeEdge;
		m_SummarizeEdgeNoPriorityVertex = m_SummarizeEdge.getMiddleShadowVertex();
		m_SummarizeEdgeEntry = m_SummarizeEdge.getEntryShadowVertex();
		m_SummarizeEdgeExit = m_SummarizeEdge.getExitShadowVertex();
		m_GameGraph = gameGraph;
		m_IsFinished = false;
		m_PriorityResult = SummarizeEdge.NO_PRIORITY;
		m_VertexToSearchPriority = new HashMap<>();
		m_SearchQueue = new LinkedList<>();

		// Start the search at spoiler invoker
		Vertex<LETTER, STATE> root = summarizeEdge.getSpoilerInvoker();
		m_VertexToSearchPriority.put(root, root.getPriority());
		m_SearchQueue.add(root);
	}

	/**
	 * Gets the priority for the given summarize edge, computed after calling
	 * {@link #search()} until {@link #isFinished()} returns <tt>true</tt>.
	 * 
	 * @return The priority for the given summarize edge or
	 *         {@link SummarizeEdge#NO_PRIORITY NO_PRIORITY} if unknown.
	 */
	public int getPriorityResult() {
		return m_PriorityResult;
	}

	/**
	 * Gets the summarize edge to compute the priority for.
	 * 
	 * @return The summarize edge to compute the priority for
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return m_SummarizeEdge;
	}

	/**
	 * Returns whether the search has finished and not got stuck. If that is the
	 * case, the value returned by {@link #getPriorityResult()} is a valid
	 * priority for the given summarize edge.
	 * 
	 * @return <tt>True</tt> if the search has finished, <tt>false</tt> if it
	 *         got stuck.
	 */
	public boolean isFinished() {
		return m_IsFinished;
	}

	/**
	 * Tries to compute the priority for the given summarize edge using a
	 * breadth-first search. A search can get stuck if other priorities are not
	 * set, it can be continued by calling this method again. The search has
	 * finished when {@link #isFinished()} returns <tt>true</tt>. After that the
	 * resulting priority can be accessed using {@link #getPriorityResult()}.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void search() throws OperationCanceledException {
		m_Logger.debug("Starting search: " + hashCode());
		boolean gotStuck = false;

		// Process queue until all vertices are processed or search got stuck
		while (!m_SearchQueue.isEmpty() && !gotStuck) {
			Vertex<LETTER, STATE> currentVertex = m_SearchQueue.peek();

			Set<Vertex<LETTER, STATE>> predecessors = m_GameGraph.getPredecessors(currentVertex);
			// Only do a search if there are predecessors, i.e. the current
			// vertex is no leaf
			if (predecessors != null) {
				for (Vertex<LETTER, STATE> pred : predecessors) {
					// Reject predecessor if it is null
					if (pred == null) {
						continue;
					}
					// Reject predecessor if it represents the summarize edge
					// for which the priority should be computed in this search.
					// Also reject if it is the entry or exit vertex of this
					// summarize edge.
					if (pred.equals(m_SummarizeEdgeNoPriorityVertex) || pred.equals(m_SummarizeEdgeEntry)
							|| pred.equals(m_SummarizeEdgeExit)) {
						continue;
					}
					// Ignore return edges
					if (pred instanceof DuplicatorDoubleDeckerVertex) {
						DuplicatorDoubleDeckerVertex<LETTER, STATE> predAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) pred;
						if (predAsDuplicatorDD.getTransitionType() == ETransitionType.RETURN) {
							continue;
						}
					}
					// If priority is unknown set gotStuck and abort
					if (pred.getPriority() == SummarizeEdge.NO_PRIORITY) {
						gotStuck = true;
						break;
					}

					// Calculate search priority for predecessor
					int optimalSuccPriority = SummarizeEdge.NO_PRIORITY;
					boolean isSpoiler = pred.isSpoilerVertex();
					int optimalValue;
					if (isSpoiler) {
						optimalValue = 1;
					} else {
						optimalValue = 0;
					}
					// Compute the optimal successor of predecessor priority
					for (Vertex<LETTER, STATE> succOfPred : m_GameGraph.getSuccessors(pred)) {
						// Reject successor if it represents the summarize edge
						// for which the priority should be computed in this
						// search.
						// Also reject if it is the entry or exit vertex of this
						// summarize edge.
						if (succOfPred.equals(m_SummarizeEdgeNoPriorityVertex)
								|| succOfPred.equals(m_SummarizeEdgeEntry) || succOfPred.equals(m_SummarizeEdgeExit)) {
							continue;
						}

						// Select priority candidate for successor of
						// predecessor
						int succOfPredPriority;
						Integer succOfPredSearchPriority = m_VertexToSearchPriority.get(succOfPred);
						// Use the search priority or the vertex priority if
						// unknown
						if (succOfPredSearchPriority != null) {
							succOfPredPriority = succOfPredSearchPriority;
						} else {
							succOfPredPriority = succOfPred.getPriority();
						}

						// Ignore successor if his priority is unknown
						if (succOfPredPriority == SummarizeEdge.NO_PRIORITY) {
							continue;
						}
						// Search for optimal value under all successors of
						// predecessor
						// If that is not present try to increase to 2
						if (succOfPredPriority > optimalSuccPriority) {
							optimalSuccPriority = succOfPredPriority;
						}
						if (succOfPredPriority == optimalValue) {
							optimalSuccPriority = succOfPredPriority;
							break;
						}
					}

					// Vertex is forced to select the minimum from the optimal
					// successor priority and its own priority
					int searchPriority;
					if (optimalSuccPriority != SummarizeEdge.NO_PRIORITY) {
						searchPriority = Math.min(optimalSuccPriority, pred.getPriority());
					} else {
						searchPriority = pred.getPriority();
					}

					// Put the search priority for the predecessor and add it to
					// the
					// queue for breadth-first processing
					Integer previousSearchPriorityValue = m_VertexToSearchPriority.put(pred, searchPriority);
					// Continue search if a search priority is new for the
					// vertex or
					// if values have changed.
					// The search will converge to a fix point since min-method
					// is
					// monotone and the set of priorities is bounded
					if (previousSearchPriorityValue == null || previousSearchPriorityValue != searchPriority) {
						m_SearchQueue.add(pred);
						m_Logger.debug("\tSetting '" + searchPriority + "' for: " + pred);
					}
				}
			}

			if (!gotStuck) {
				m_SearchQueue.poll();
			} else {
				m_Logger.debug("Got stuck: " + hashCode());
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
				m_Logger.debug("Stopped in search");
				throw new OperationCanceledException(this.getClass());
			}
		}

		// Queue was completely processed without getting stuck
		if (m_SearchQueue.isEmpty() && !gotStuck) {
			// Finish search and compute the result
			Integer searchPriorityResult = m_VertexToSearchPriority.get(m_SummarizeEdge.getSource());
			if (searchPriorityResult != SummarizeEdge.NO_PRIORITY) {
				m_PriorityResult = searchPriorityResult;
				m_IsFinished = true;
			} else {
				// TODO Solve cyclic dependency problems
				throw new IllegalStateException(
						"Computing summarize edge priority could not be done. Somehow the source of the edge was no search priority though it was processed by the search.");
			}
		}
	}
}
