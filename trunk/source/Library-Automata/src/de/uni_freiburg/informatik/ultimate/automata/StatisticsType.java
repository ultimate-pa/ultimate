/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License as published
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
package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaSimulationBased;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;

/**
 * Type of statistics that can be reported to the
 * {@link de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics AutomataOperationStatistics} class.
 * <p>
 * The fields are used as keys in the statistics map.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public enum StatisticsType {
	/**
	 * Number of call symbols.
	 */
	ALPHABET_SIZE_CALL,
	/**
	 * Number of internal symbols.
	 */
	ALPHABET_SIZE_INTERNAL,
	/**
	 * Number of return symbols.
	 */
	ALPHABET_SIZE_RETURN,
	/**
	 * One if the game automaton of a nwa game graph already was deterministic before using the determinizer, zero or
	 * not set else (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	ALREADY_WAS_DETERMINISTIC,
	/**
	 * Identification of the operation in the ats file.
	 */
	ATS_ID,
	/**
	 * Size of the alphabet the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_NONDETERMINISTIC_STATES,
	/**
	 * Amount of transitions the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has before simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_RETURN,
	/**
	 * The call transition density the automaton has before simulation multiplied with 1_000_000, then rounded (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has before simulation multiplied with 1_000_000, then rounded (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has before simulation multiplied with 1_000_000, then rounded (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has before simulation multiplied with 1_000_000, then rounded (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * The time building the game graph took (used in simulation, for compatibility with {@link ETimeMeasure}).
	 */
	BUILD_GRAPH,
	/**
	 * The time building the result automaton took.
	 */
	BUILD_RESULT,
	/**
	 * The time building the SCC took, SCC is an optimization for automata.
	 */
	BUILD_SCC,
	/**
	 * The time needed for computing which vertex down states are safe (used in simulation, for compatibility with
	 * {@link ETimeMeasure}).
	 */
	COMPUTE_SAFE_VERTEX_DOWN_STATES,
	/**
	 * The time computing priorities for summarize edges took in nwa game graph generation (used in simulation, for
	 * compatibility with {@link ETimeMeasure}).
	 */
	COMPUTE_SUMMARIZE_EDGE_PRIORITIES,
	/**
	 * The amount of states the determinized game automaton has (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	DETERMINIZED_GAME_AUTOMATON_STATES,
	/**
	 * Number of transitions for which we checked if there are corresponding events
	 * that have to be added to the possible extensions.
	 */
	EXTENSION_CANDIDATES_TOTAL,
	/**
	 * Number of transitions for which we checked if there are corresponding events
	 * that have to be added to the possible extensions, but we could not find such
	 * an event.
	 */
	EXTENSION_CANDIDATES_USELESS,
	/**
	 * Amount of merge attempts that where aborted (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	FAILED_MERGE_ATTEMPTS,
	/**
	 * Amount of transition removal attempts that where aborted (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	FAILED_TRANSREMOVE_ATTEMPTS,
	/**
	 * Amount of edges the game graph has (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	GAMEGRAPH_EDGES,
	/**
	 * Amount of vertices the game graph has (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	GAMEGRAPH_VERTICES,
	/**
	 * The time generating summarize edges took in nwa game graph generation (used in simulation, for compatibility with
	 * {@link ETimeMeasure}).
	 */
	GENERATE_SUMMARIZE_EDGES,
	/**
	 * The global bound for infinty (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	GLOBAL_INFINITY,
	/**
	 * If the operation has timed out.
	 */
	HAS_TIMED_OUT,
	/**
	 * Result of an inclusion check.
	 */
	IS_INCLUDED,
	/**
	 * If the operation ran out of memory.
	 */
	IS_OUT_OF_MEMORY,
	/**
	 * If the operation uses SCC, an optimization for automata.
	 */
	IS_USING_SCCS,
	/**
	 * Max number of duplicator DoubleDeckers in a node of the game automaton.
	 */
	MAX_NUMBER_OF_DOUBLEDECKER_PEBBLES,
	/**
	 * Number of clauses.
	 */
	NUMBER_CLAUSES,
	/**
	 * Number of conditions in a {@link BranchingProcess}.
	 */
	NUMBER_CONDITIONS,
	/**
	 * Number of pairs of conditions for which we checked whether they are in co-relation while computing the
	 * unfolding of a Petri net.
	 */
	NUMBER_CO_RELATION_QUERIES,
	/**
	 * Number of cut-off events in Petri net unfolding.
	 */
	NUMBER_CUT_OFF_EVENTS,
	/**
	 * Number of pairs in a preprocessing.
	 */
	NUMBER_INITIAL_PAIRS,
	/**
	 * Number of pairs in a preprocessing for PMax-SAT solver.
	 */
	NUMBER_INITIAL_PAIRS_PMAXSAT,
	/**
	 * Number of events in Petri net unfolding that are not cut-off events.
	 */
	NUMBER_NON_CUT_OFF_EVENTS,
	/**
	 * Number of pairs in a result.
	 */
	NUMBER_RESULT_PAIRS,
	/**
	 * Number of transitions that can never fire in a Petri net.
	 */
	NUMBER_UNREACHABLE_TRANSITIONS,
	/**
	 * Number of variables.
	 */
	NUMBER_VARIABLES,
	/**
	 * Operation name.
	 */
	OPERATION_NAME,
	/**
	 * Size of the alphabet of a Petri net.
	 */
	PETRI_ALPHABET,
	/**
	 * Size of the flow relation / number of edges inside a Petri net
	 * that is used as the minuend of a difference operation.
	 */
	PETRI_DIFFERENCE_MINUEND_FLOW,
	/**
	 * Number of places inside a Petri net that is used as the minuend of a difference operation.
	 */
	PETRI_DIFFERENCE_MINUEND_PLACES,
	/**
	 * Number of transitions inside a Petri net that is used as the minuend of a difference operation.
	 */
	PETRI_DIFFERENCE_MINUEND_TRANSITIONS,
	/**
	 * Number of letters in subtrahend's alphabet that are
	 * used more often to label non-self-loops than self-loops in subtrahend.
	 */
	PETRI_DIFFERENCE_SUBTRAHEND_LETTERS_WITH_MORE_CHANGERS_THAN_LOOPERS,
	/**
	 * Number of letters in subtrahend's alphabet that are only used to label only self-loops in subtrahend.
	 */
	PETRI_DIFFERENCE_SUBTRAHEND_LOOPER_ONLY_LETTERS,
	/**
	 * Number of states in an NWA that is used as the subtrahend of a difference operation.
	 */
	PETRI_DIFFERENCE_SUBTRAHEND_STATES,
	/**
	 * Size of the flow relation / number of edges inside a Petri net.
	 */
	PETRI_FLOW,
	/**
	 * Number of places inside a Petri net.
	 */
	PETRI_PLACES,
	/**
	 * Number of Petri net flow edges removed by an operation.
	 */
	PETRI_REMOVED_FLOW,
	/**
	 * Number of Petri net places removed by an operation.
	 */
	PETRI_REMOVED_PLACES,
	/**
	 * Number of Petri net transitions removed by an operation.
	 */
	PETRI_REMOVED_TRANSITIONS,
	/**
	 * Number of transitions inside a Petri net.
	 */
	PETRI_TRANSITIONS,
	/**
	 * Amount of transitions a simulation has removed (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	REMOVED_TRANSITIONS,
	/**
	 * Size of the alphabet the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_NONDETERMINISTIC_STATES,
	/**
	 * Amount of transitions the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has after simulation (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_RETURN,
	/**
	 * The call transition density the automaton has after simulation multiplied with 1_000_000, then rounded (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has after simulation multiplied with 1_000_000, then rounded (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has after simulation multiplied with 1_000_000, then rounded (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has after simulation multiplied with 1_000_000, then rounded (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * Tells whether right-hand side operand is deterministic.
	 */
	RHS_IS_DETERMINISTIC,
	/**
	 * Tells whether right-hand side operand semi-deterministic.
	 */
	RHS_IS_SEMIDETERMINISTIC,
	/**
	 * Total runtime.
	 */
	RUNTIME_TOTAL_MS,
	/**
	 * Amount of SCCs the game graph has (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	SCCS,
	/**
	 * The time the simulation only took, this is the overall time minus the time to build the graph and the result
	 * (used in simulation, for compatibility with {@link ETimeMeasure}).
	 */
	SIMULATION_ONLY,
	/**
	 * Amount of steps a simulation needed (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	SIMULATION_STEPS,
	/**
	 * Number of states of a game automaton which is e.g., constructed in {@link ReduceNwaSimulationBased}.
	 */
	SIZE_GAME_AUTOMATON,
	/**
	 * Number of nodes of a game graph that is used to compute simulation relations.
	 */
	SIZE_GAME_GRAPH,
	/**
	 * Number of blocks in an initial partition.
	 */
	SIZE_INITIAL_PARTITION,
	/**
	 * Number of blocks in an initial partition for PMax-SAT solver.
	 */
	SIZE_INITIAL_PARTITION_PMAXSAT,
	/**
	 * Number of states in the biggest block of an initial partition.
	 */
	SIZE_MAXIMAL_INITIAL_BLOCK,
	/**
	 * Number of states in the biggest block of an initial partition for PMax-SAT solver.
	 */
	SIZE_MAXIMAL_INITIAL_BLOCK_PMAXSAT,
	/**
	 * The time solving the Max-Sat problem at nwa game graph resulting automaton generation took (used in simulation,
	 * for compatibility with {@link ETimeMeasure}).
	 */
	SOLVE_MAX_SAT,
	/**
	 * Number of states in the input.
	 */
	STATES_INPUT,
	/**
	 * Number of states in the left-hand side input operand.
	 */
	STATES_LHS,
	/**
	 * Number of states in the input.
	 */
	STATES_OUTPUT,
	/**
	 * Absolute difference in the number of states between input and output.
	 */
	STATES_REDUCTION_ABSOLUTE,
	/**
	 * Relative difference in the number of states between input and output.
	 */
	STATES_REDUCTION_RELATIVE,
	/**
	 * Number of states in the right-hand side input operand.
	 */
	STATES_RHS,
	/**
	 * Amount of sub-summarize edges a nwa game graph has (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	SUB_SUMMARIZE_EDGES,
	/**
	 * Amount of summarize edges a nwa game graph has (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	SUMMARIZE_EDGES,
	/**
	 * Run time for asserting clauses.
	 */
	TIME_ASSERTING,
	/**
	 * Run time for preprocessing.
	 */
	TIME_PREPROCESSING,
	/**
	 * Run time for simulation.
	 */
	TIME_SIMULATION,
	/**
	 * Run time for old simulation implementation.
	 */
	@Deprecated
	TIME_SIMULATION_OLD,
	/**
	 * Run time for solving.
	 */
	TIME_SOLVING,
	/**
	 * Number of call transitions.
	 */
	TRANSITIONS_CALL_INPUT,
	/**
	 * Number of call transitions.
	 */
	TRANSITIONS_CALL_OUTPUT,
	/**
	 * Total number of transitions (call+internal+return).
	 */
	TRANSITIONS_INPUT,
	/**
	 * Number of internal transitions.
	 */
	TRANSITIONS_INTERNAL_INPUT,
	/**
	 * Number of internal transitions.
	 */
	TRANSITIONS_INTERNAL_OUTPUT,
	/**
	 * Total number of transitions  (call+internal+return).
	 */
	TRANSITIONS_OUTPUT,
	/**
	 * Absolute difference in the number of transitions between input and output.
	 */
	TRANSITIONS_REDUCTION_ABSOLUTE,
	/**
	 * Relative difference in the number of transitions between input and output.
	 */
	TRANSITIONS_REDUCTION_RELATIVE,
	/**
	 * Number of return transitions.
	 */
	TRANSITIONS_RETURN_INPUT,
	/**
	 * Number of return transitions.
	 */
	TRANSITIONS_RETURN_OUTPUT,

}







