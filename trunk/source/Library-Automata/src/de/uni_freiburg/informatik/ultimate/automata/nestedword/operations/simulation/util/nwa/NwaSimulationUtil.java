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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.INwaGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Provides utility methods for simulation with NWA automata.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class NwaSimulationUtil {
	private NwaSimulationUtil() {
		// Utility class.
	}

	/**
	 * Checks if the simulation results saved in the given game graph are correct.<br>
	 * This is only a semi-check, i.e., if it returns {@code false}, there is a violation. For instance, we ignore
	 * return transitions.
	 * 
	 * @param gameGraph
	 *            Game graph where the simulation results are saved in
	 * @param nwa
	 *            The underlying NWA
	 * @param simulationType
	 *            simulation type
	 * @param isInitialPairPredicate
	 *            returns {@code true} iff a given pair of states is initial
	 * @param logger
	 *            logger
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return {@code false} only if the simulation results are not correct (however, {@code true} has no meaning)
	 */
	public static <LETTER, STATE> boolean areNwaSimulationResultsCorrect(final AGameGraph<LETTER, STATE> gameGraph,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final ESimulationType simulationType,
			final BiPredicate<STATE, STATE> isInitialPairPredicate, final ILogger logger) {
		if (logger.isInfoEnabled()) {
			logger.info("Starting checking correctness of simulation results.");
		}

		// We check each supposed simulation and validate
		// First collect them
		final HashRelation<STATE, STATE> supposedSimulations = new HashRelation<>();
		for (final SpoilerVertex<LETTER, STATE> spoilerVertex : gameGraph.getSpoilerVertices()) {
			// skip auxiliary vertices
			if (!(spoilerVertex instanceof SpoilerNwaVertex<?, ?>)) {
				continue;
			}

			// All the states we need are from Spoiler
			final STATE state1 = spoilerVertex.getQ0();
			final STATE state2 = spoilerVertex.getQ1();

			// Ignore special cases
			if (state1 == null || state2 == null) {
				continue;
			}

			final boolean considerVertex;
			if (simulationType == ESimulationType.DELAYED) {
				// For delayed simulation we need to choose between the vertex with bit set to true or false
				if (spoilerVertex.isB()) {
					considerVertex = nwa.isFinal(state1) && !nwa.isFinal(state2);
				} else {
					considerVertex = !nwa.isFinal(state1) || nwa.isFinal(state2);
				}
			} else {
				considerVertex = true;
			}

			if (considerVertex
					&& (spoilerVertex.getPM(null, gameGraph.getGlobalInfinity()) < gameGraph.getGlobalInfinity())) {
				supposedSimulations.addPair(spoilerVertex.getQ0(), spoilerVertex.getQ1());
			}
		}

		// Validate the supposed simulations
		for (final Entry<STATE, STATE> supposedSimulation : supposedSimulations.entrySet()) {
			final STATE leftState = supposedSimulation.getKey();
			final STATE rightState = supposedSimulation.getValue();
			if (!isInitialPairPredicate.test(leftState, rightState)) {
				// ignore states that are not considered by the user
				continue;
			}

			// internal successors
			if (!findSuccessorSimulationWitness(logger, supposedSimulations, leftState, rightState,
					isInitialPairPredicate, () -> nwa.internalSuccessors(leftState), nwa::internalSuccessors)) {
				return false;
			}

			// call successors
			if (!findSuccessorSimulationWitness(logger, supposedSimulations, leftState, rightState,
					isInitialPairPredicate, () -> nwa.callSuccessors(leftState), nwa::callSuccessors)) {
				return false;
			}

			// Return transitions do not need to get matched
		}

		if (logger.isInfoEnabled()) {
			logger.info("Finished checking correctness of simulation results, they are correct.");
		}
		return true;
	}

	private static <LETTER, STATE> boolean findSuccessorSimulationWitness(final ILogger logger,
			final HashRelation<STATE, STATE> supposedSimulations, final STATE leftState, final STATE rightState,
			final BiPredicate<STATE, STATE> isInitialPairPredicate,
			final Supplier<Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>>> succFromState,
			final BiFunction<STATE, LETTER, Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>>> succFromStateAndLetter) {
		// Each from leftState outgoing transitions also needs an matching
		// outgoing transition from rightState whose destination also
		// simulates the other
		// Internal transitions
		for (final IOutgoingTransitionlet<LETTER, STATE> leftTrans : succFromState.get()) {
			final STATE leftDest = leftTrans.getSucc();
			final LETTER letter = leftTrans.getLetter();
			final Set<STATE> destinationSimulation = supposedSimulations.getImage(leftDest);

			boolean foundMatchingTrans = false;
			for (final IOutgoingTransitionlet<LETTER, STATE> rightTrans : succFromStateAndLetter.apply(rightState,
					letter)) {
				final STATE rightDest = rightTrans.getSucc();
				// If the right destination also simulates the left
				// destination, we found a matching transition
				if (destinationSimulation.contains(rightDest)) {
					foundMatchingTrans = true;
					break;
				}
				if (!isInitialPairPredicate.test(leftDest, rightDest)) {
					// we should ignore cases where one successor pair is not considered by the user
					return true;
				}
			}

			// If no matching transition could be found, the underlying
			// simulation is incorrect
			if (!foundMatchingTrans) {
				if (logger.isDebugEnabled()) {
					logger.debug("Supposedly " + rightState + " simulates " + leftState
							+ ". But there is no matching partner for " + leftTrans);
				}
				return false;
			}
		}
		return true;
	}

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
		final Queue<Vertex<LETTER, STATE>> workingList = new LinkedList<>();
		final int globalInfinity = gameGraph.getGlobalInfinity();
		final Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = gameGraph.getSpoilerVertices();
		if (spoilerVertices != null) {
			for (final SpoilerVertex<LETTER, STATE> spoilerVertex : gameGraph.getSpoilerVertices()) {
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
			final Vertex<LETTER, STATE> workingVertex = workingList.poll();

			// Impose every predecessor, that is no call predecessor, a progress
			// measure of infinity. If they are Duplicator vertices, do that
			// only if they have no other simulating successors
			if (!gameGraph.hasPredecessors(workingVertex)) {
				continue;
			}
			for (final Vertex<LETTER, STATE> pred : gameGraph.getPredecessors(workingVertex)) {
				// Ignore the predecessor if he already has a progress measure
				// of infinity
				if (pred.getPM(null, globalInfinity) >= globalInfinity) {
					continue;
				}
				// Ignore call predecessors
				if (pred instanceof DuplicatorNwaVertex<?, ?>) {
					final DuplicatorNwaVertex<LETTER, STATE> predAsNwa = (DuplicatorNwaVertex<LETTER, STATE>) pred;
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
						for (final Vertex<LETTER, STATE> succ : gameGraph.getSuccessors(pred)) {
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
	 * Retrieves general performance data of the input and output nwa automaton.
	 * Saves the data in the given internal performance object. Only nwa
	 * specific information are saved, thus it can be used together with the
	 * more general version of {@link ASimulation}.
	 * 
	 * @param simulationPerformance
	 *            Performance object to save the data in
	 * @param input
	 *            The input nwa automaton
	 * @param result
	 *            The resulting nwa automaton
	 * @param services
	 *            The service object used by the framework
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	public static <LETTER, STATE> void retrieveGeneralNwaAutomataPerformance(
			final SimulationPerformance simulationPerformance, final INestedWordAutomaton<LETTER, STATE> input,
			final INestedWordAutomaton<LETTER, STATE> result, final AutomataLibraryServices services) {
		final Analyze<LETTER, STATE> inputAnalyzer = new Analyze<>(services, input, true);

		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_ALPHABET_SIZE_INTERNAL,
				inputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_ALPHABET_SIZE_CALL,
				inputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_ALPHABET_SIZE_RETURN,
				inputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));

		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS_INTERNAL,
				inputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS_CALL,
				inputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS_RETURN,
				inputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));

		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.INTERNAL) * 1_000_000));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITION_CALL_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.CALL) * 1_000_000));
		simulationPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITION_RETURN_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.RETURN) * 1_000_000));

		final Analyze<LETTER, STATE> outputAnalyzer = new Analyze<>(services, result, true);

		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_ALPHABET_SIZE_INTERNAL,
				outputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_ALPHABET_SIZE_CALL,
				outputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_ALPHABET_SIZE_RETURN,
				outputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));

		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITIONS_INTERNAL,
				outputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITIONS_CALL,
				outputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITIONS_RETURN,
				outputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));

		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITION_INTERNAL_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.INTERNAL) * 1_000_000));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITION_CALL_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.CALL) * 1_000_000));
		simulationPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITION_RETURN_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.RETURN) * 1_000_000));
	}

	/**
	 * Predicate representing a binary relation that is backed by a partition.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <STATE>
	 *            state type
	 */
	public static class BinaryRelationPredicateFromPartition<STATE> implements BiPredicate<STATE, STATE> {
		private final Map<STATE, Set<STATE>> mState2states;

		/**
		 * @param partition
		 *            Partition.
		 */
		public BinaryRelationPredicateFromPartition(final Iterable<Set<STATE>> partition) {
			mState2states = new HashMap<>();
			for (final Set<STATE> block : partition) {
				for (final STATE state : block) {
					mState2states.put(state, block);
				}
			}
		}

		@SuppressWarnings("squid:S1698")
		@Override
		public boolean test(final STATE state1, final STATE state2) {
			// equality intended here
			return mState2states.get(state1) == mState2states.get(state2);
		}
	}
}
