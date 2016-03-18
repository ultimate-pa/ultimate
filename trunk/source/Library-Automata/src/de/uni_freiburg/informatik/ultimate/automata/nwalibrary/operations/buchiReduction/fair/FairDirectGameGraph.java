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
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Game graph that realizes <b>fair and direct simulation</b>. It primarily uses
 * fair simulation and uses direct simulation as an optimization.<br/>
 * In fair simulation each time <i>Spoiler</i> builds an accepting word
 * <i>Duplicator</i>s word must also be accepting.<br/>
 * In direct simulation each time <i>Spoiler</i> visits an accepting state
 * <i>Duplicator</i> must also do so.<br/>
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
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class FairDirectGameGraph<LETTER, STATE> extends FairGameGraph<LETTER, STATE> {

	/**
	 * Stores information about vertices that, interpreted as (q0, q1),
	 * represent a simulation where q1 direct simulates q0.
	 */
	private final Set<SpoilerVertex<LETTER, STATE>> m_DirectSimulations;

	/**
	 * Stores information about all edges that need to be removed if
	 * transforming from direct to a fair game graph, added for the other
	 * direction.
	 */
	private HashSet<Pair<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>>> m_EdgesToBeChangedForTransformation;

	/**
	 * True if the game graph currently mimics the behavior of a
	 * DirectGameGraph, false if it mimics a FairGameGraph.
	 */
	private boolean m_IsCurrentlyDirectGameGraph;

	/**
	 * Creates a new fair direct game graph by using the given buechi automaton.
	 * After construction it mimics the behavior of a FairGameGraph, it can be
	 * transformed to a DirectGameGraph using
	 * {@link #transformToDirectGameGraph()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            Logger of the Ultimate framework.
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
	public FairDirectGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final Logger logger, final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(services, progressTimer, logger, buechi, stateFactory);
		if (!buechi.getCallAlphabet().isEmpty() || !buechi.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException(
					"The inputed automaton is no Buechi-automaton. It must have an empty call and return alphabet.");
		}
		m_IsCurrentlyDirectGameGraph = false;
		m_DirectSimulations = new HashSet<>();
		m_EdgesToBeChangedForTransformation = new HashSet<>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	public void generateGameGraphFromBuechi() throws OperationCanceledException {
		super.generateGameGraphFromBuechi();
		calculateTransformationChanges();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#getGlobalInfinity()
	 */
	@Override
	public int getGlobalInfinity() {
		if (m_IsCurrentlyDirectGameGraph) {
			// In a direct game graph the global infinity is 1
			return 1;
		} else {
			// Use the original fair priority
			return super.getGlobalInfinity();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#getPriority(de.uni_freiburg.informatik.ultimate
	 * .automata.nwalibrary.operations.buchiReduction.vertices.Vertex)
	 */
	@Override
	public int getPriority(Vertex<LETTER, STATE> vertex) {
		if (m_IsCurrentlyDirectGameGraph) {
			// In a direct game graph every vertex has priority 0
			return 0;
		} else {
			// Use the original fair priority
			return vertex.getPriority();
		}
	}

	/**
	 * Returns if the given vertex, interpreted as (q0, q1), represents a
	 * simulation where q1 direct simulates q0.<br/>
	 * This needs a previous made direct simulation and usage of the method
	 * {@link #rememberAndClearDirectSimulationResults()} in order to work.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return True if vertex, interpreted as (q0, q1), represents a simulation
	 *         where q1 direct simulates q0, false if not.
	 */
	public boolean isDirectSimulating(SpoilerVertex<LETTER, STATE> vertex) {
		return m_DirectSimulations.contains(vertex) || vertex.getQ0().equals(vertex.getQ1());
	}

	/**
	 * Calculates which edges need to be removed if transforming from direct to
	 * a fair game graph, added for the other direction.
	 */
	private void calculateTransformationChanges() {
		for (Vertex<LETTER, STATE> vertex : getVertices()) {
			// Priority 1 reflects (q0, q1) where q0 is final and q1 is not.
			// This vertices need to be excluded for direct simulation
			if (vertex.getPriority() == 1) {
				if (hasSuccessors(vertex)) {
					for (Vertex<LETTER, STATE> succ : getSuccessors(vertex)) {
						m_EdgesToBeChangedForTransformation.add(new Pair<>(vertex, succ));
					}
				}
				if (hasPredecessors(vertex)) {
					for (Vertex<LETTER, STATE> pred : getPredecessors(vertex)) {
						m_EdgesToBeChangedForTransformation.add(new Pair<>(pred, vertex));
					}
				}
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.fair.FairGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	protected INestedWordAutomatonOldApi<LETTER, STATE> generateBuchiAutomatonFromGraph()
			throws OperationCanceledException {
		if (m_IsCurrentlyDirectGameGraph) {
			// For the direct simulation we won't generate an expensive unused
			// result since we only need the progress measure results for
			// optimization, not the resulting automaton.
			return null;
		} else {
			// Use the original fair generation
			return super.generateBuchiAutomatonFromGraph();
		}
	}

	/**
	 * Returns if the game graph currently mimics the behavior of a
	 * DirectGameGraph or a FairGameGraph.
	 * 
	 * @return True if the game graph currently mimics the behavior of a
	 *         DirectGameGraph, false if it mimics a FairGameGraph.
	 */
	protected boolean isCurrentlyDirectGameGraph() {
		return m_IsCurrentlyDirectGameGraph;
	}

	/**
	 * Remembers the result of a made direct simulation and clears all made
	 * changes to values of all vertices.<br/>
	 * This is mainly used after a direct simulation and before the
	 * transformation to a FairGameGraph.
	 */
	protected void rememberAndClearDirectSimulationResults() {
		// Remember direct simulations
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = getSpoilerVertices();
		for (SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}
				// Found a one-directed direct simulating pair
				m_DirectSimulations.add(vertex);
			}

			// Clear changes made in simulation
			vertex.setPM(0);
			vertex.setBEff(0);
			vertex.setC(0);
		}

		// Also clear changes made on duplicator vertices
		Set<DuplicatorVertex<LETTER, STATE>> duplicatorVertices = getDuplicatorVertices();
		for (DuplicatorVertex<LETTER, STATE> vertex : duplicatorVertices) {
			vertex.setPM(0);
			vertex.setBEff(0);
			vertex.setC(0);
		}
	}

	/**
	 * Transforms the game graph to a DirectGameGraph, it then mimics its
	 * behavior.
	 */
	protected void transformToDirectGameGraph() {
		if (m_IsCurrentlyDirectGameGraph) {
			return;
		}

		// Remove the corresponding edges
		for (Pair<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>> edge : m_EdgesToBeChangedForTransformation) {
			removeEdge(edge.getFirst(), edge.getSecond());
		}

		m_IsCurrentlyDirectGameGraph = true;
	}

	/**
	 * Transforms the game graph to a FairGameGraph, it then mimics its
	 * behavior.
	 */
	protected void transformToFairGameGraph() {
		if (!m_IsCurrentlyDirectGameGraph) {
			return;
		}

		// Add the corresponding edges
		for (Pair<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>> edge : m_EdgesToBeChangedForTransformation) {
			addEdge(edge.getFirst(), edge.getSecond());
		}

		m_IsCurrentlyDirectGameGraph = false;
	}
}
