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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ETimeMeasure;

/**
 * Type of statistics that can be reported to the
 * {@link de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics
 * AutomataOperationStatistics} class.
 * <p>
 * The fields are used as keys in the statistics map.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Tischner
 */
public enum StatisticsType {
	/**
	 * One if the game automaton of a nwa game graph already was deterministic
	 * before using the determinizer, zero or not set else (used in simulation,
	 * for compatibility with {@link ECountingMeasure}).
	 */
	ALREADY_WAS_DETERMINISTIC,
	/**
	 * Identification of the operation in the ats file.
	 */
	ATS_ID,
	/**
	 * Size of the alphabet the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has before simulation (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has before simulation
	 * (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_NONDETERMINISTIC_STATES,
	/**
	 * The call transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has before simulation multiplied
	 * with 1_000_000, then rounded (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * Amount of transitions the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has before simulation (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has before simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	BUCHI_TRANSITIONS_RETURN,
	/**
	 * The time building the game graph took (used in simulation, for
	 * compatibility with {@link ETimeMeasure}).
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
	 * The time needed for computing which vertex down states are safe (used in
	 * simulation, for compatibility with {@link ETimeMeasure}).
	 */
	COMPUTE_SAFE_VERTEX_DOWN_STATES,
	/**
	 * The time computing priorities for summarize edges took in nwa game graph
	 * generation (used in simulation, for compatibility with
	 * {@link ETimeMeasure}).
	 */
	COMPUTE_SUMMARIZE_EDGE_PRIORITIES,
	/**
	 * The amount of states the determinized game automaton has (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	DETERMINIZED_GAME_AUTOMATON_STATES,
	/**
	 * Amount of merge attempts that where aborted (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	FAILED_MERGE_ATTEMPTS,
	/**
	 * Amount of transition removal attempts that where aborted (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	FAILED_TRANSREMOVE_ATTEMPTS,
	/**
	 * Amount of edges the game graph has (used in simulation, for compatibility
	 * with {@link ECountingMeasure}).
	 */
	GAMEGRAPH_EDGES,
	/**
	 * Amount of vertices the game graph has (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	GAMEGRAPH_VERTICES,
	/**
	 * The time generating summarize edges took in nwa game graph generation
	 * (used in simulation, for compatibility with {@link ETimeMeasure}).
	 */
	GENERATE_SUMMARIZE_EDGES,
	/**
	 * The global bound for infinty (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	GLOBAL_INFINITY,
	/**
	 * If the operation has timed out.
	 */
	HAS_TIMED_OUT,
	/**
	 * If the operation ran out of memory.
	 */
	IS_OUT_OF_MEMORY,
	/**
	 * If the operation uses SCC, an optimization for automata
	 */
	IS_USING_SCCS,
	/**
	 * Operation name.
	 */
	OPERATION_NAME,
	/**
	 * Amount of transitions a simulation has removed (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	REMOVED_TRANSITIONS,
	/**
	 * Size of the alphabet the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has after simulation
	 * (used in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_NONDETERMINISTIC_STATES,
	/**
	 * The call transition density the automaton has after simulation multiplied
	 * with 1_000_000, then rounded (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has after simulation multiplied with
	 * 1_000_000, then rounded (used in simulation, for compatibility with
	 * {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has after simulation
	 * multiplied with 1_000_000, then rounded (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has after simulation
	 * multiplied with 1_000_000, then rounded (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * Amount of transitions the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has after simulation (used
	 * in simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has after simulation (used in
	 * simulation, for compatibility with {@link ECountingMeasure}).
	 */
	RESULT_TRANSITIONS_RETURN,
	/**
	 * Total runtime.
	 */
	RUNTIME_TOTAL,
	/**
	 * Amount of SCCs the game graph has (used in simulation, for compatibility
	 * with {@link ECountingMeasure}).
	 */
	SCCS,
	/**
	 * The time the simulation only took, this is the overall time minus the
	 * time to build the graph and the result (used in simulation, for
	 * compatibility with {@link ETimeMeasure}).
	 */
	SIMULATION_ONLY,
	/**
	 * Amount of steps a simulation needed (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	SIMULATION_STEPS,
	/**
	 * The time solving the Max-Sat problem at nwa game graph resulting
	 * automaton generation took (used in simulation, for compatibility with
	 * {@link ETimeMeasure}).
	 */
	SOLVE_MAX_SAT,
	/**
	 * Number of states in the input.
	 */
	STATES_INPUT,
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
	 * Amount of sub-summarize edges a nwa game graph has (used in simulation,
	 * for compatibility with {@link ECountingMeasure}).
	 */
	SUB_SUMMARIZE_EDGES,
	/**
	 * Amount of summarize edges a nwa game graph has (used in simulation, for
	 * compatibility with {@link ECountingMeasure}).
	 */
	SUMMARIZE_EDGES
}
