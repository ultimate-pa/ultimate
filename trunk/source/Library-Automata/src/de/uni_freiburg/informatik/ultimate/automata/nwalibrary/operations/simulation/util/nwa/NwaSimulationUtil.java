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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Provides utility methods for simulation with NWA automata.
 * 
 * @author Daniel Tischner
 *
 */
public final class NwaSimulationUtil {

	/**
	 * Computes the <i>inner simulation</i> on a given nwa game graph. The
	 * simulation makes predecessors of non-simulating vertices also to
	 * non-simulating vertices. In the case of Duplicator vertices this only
	 * happens if they have no other simulating successors. The simulation
	 * allows propagation over return, summarize and internal edges, but
	 * disallows it over call edges.
	 * 
	 * @param <LETTER>
	 *            Letter class of nwa automaton
	 * @param <STATE>
	 *            State class of nwa automaton
	 * @param gameGraph
	 *            The nwa game graph to do the simulation on
	 * @param logger
	 *            ILogger of the Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	@SuppressWarnings("unchecked")
	public static <LETTER, STATE> void doInnerNwaSimulation(final AGameGraph<LETTER, STATE> gameGraph,
			final ILogger logger, final IProgressAwareTimer progressTimer) throws AutomataOperationCanceledException {
		if (logger.isDebugEnabled()) {
			logger.debug("Starting innerSimulation.");
		}

		// Undo removing of return bridges
		if (gameGraph instanceof INwaGameGraph<?, ?>) {
			((INwaGameGraph<LETTER, STATE>) gameGraph).undoRemovedReturnBridgesChanges();
		} else {
			throw new IllegalArgumentException("The given gameGraph must be an instance of INwaGameGraph.");
		}

		// Collect all non simulating vertices
		Queue<Vertex<LETTER, STATE>> workingList = new LinkedList<>();
		int globalInfinity = gameGraph.getGlobalInfinity();
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = gameGraph.getSpoilerVertices();
		if (spoilerVertices != null) {
			for (SpoilerVertex<LETTER, STATE> spoilerVertex : gameGraph.getSpoilerVertices()) {
				if (spoilerVertex.getPM(null, globalInfinity) >= globalInfinity) {
					workingList.add(spoilerVertex);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (progressTimer != null && !progressTimer.continueProcessing()) {
					logger.debug("Stopped in doInnerNwaSimulation/collecting non simulating vertices");
					throw new AutomataOperationCanceledException(NwaSimulationUtil.class);
				}
			}
		}

		// Start the simulation, beginning with all roots
		while (!workingList.isEmpty()) {
			Vertex<LETTER, STATE> workingVertex = workingList.poll();

			// Impose every predecessor, that is no call predecessor, a progress
			// measure of infinity. If they are Duplicator vertices, do that
			// only if they have no other simulating successors
			if (!gameGraph.hasPredecessors(workingVertex)) {
				continue;
			}
			for (Vertex<LETTER, STATE> pred : gameGraph.getPredecessors(workingVertex)) {
				// Ignore the predecessor if he already has a progress measure
				// of infinity
				if (pred.getPM(null, globalInfinity) >= globalInfinity) {
					continue;
				}
				// Ignore call predecessors
				if (pred instanceof DuplicatorNwaVertex<?, ?>) {
					DuplicatorNwaVertex<LETTER, STATE> predAsNwa = (DuplicatorNwaVertex<LETTER, STATE>) pred;
					if (predAsNwa.getTransitionType() == ETransitionType.CALL) {
						continue;
					}
				}

				boolean considerVertex = true;
				// If the predecessor is a duplicator vertex, check if he has an
				// alternative successor
				if (pred instanceof DuplicatorVertex<?, ?>) {
					boolean hasAlternative = false;
					if (gameGraph.hasSuccessors(pred)) {
						for (Vertex<LETTER, STATE> succ : gameGraph.getSuccessors(pred)) {
							// We not need to explicitly ignore call and
							// summarize successors since successors of
							// Duplicator vertices are always Spoiler vertices.
							if (succ.getPM(null, globalInfinity) < globalInfinity) {
								hasAlternative = true;
								break;
							}
						}
					}
					// Only consider the Duplicator vertex if he has no
					// alternative
					considerVertex = !hasAlternative;
				}

				// Impose a progress measure of infinity and add the element
				if (considerVertex) {
					pred.setPM(globalInfinity);
					workingList.add(pred);

					if (logger.isDebugEnabled()) {
						logger.debug("\tImposed infinity for: " + pred);
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (progressTimer != null && !progressTimer.continueProcessing()) {
					logger.debug("Stopped in doInnerNwaSimulation/processing predecessors");
					throw new AutomataOperationCanceledException(NwaSimulationUtil.class);
				}
			}
		}
	}

	/**
	 * Utility class. No implementation.
	 */
	private NwaSimulationUtil() {

	}
}
