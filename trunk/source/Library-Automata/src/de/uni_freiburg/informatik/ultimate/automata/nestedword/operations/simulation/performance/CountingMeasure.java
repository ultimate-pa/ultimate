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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

/**
 * Different types of counting measures.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public enum CountingMeasure {
	/**
	 * One if the game automaton of a nwa game graph already was deterministic
	 * before using the determinizer, zero or not set else.
	 */
	ALREADY_WAS_DETERMINISTIC,
	/**
	 * Size of the alphabet the automaton has before simulation.
	 */
	BUCHI_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has before simulation.
	 */
	BUCHI_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has before simulation.
	 */
	BUCHI_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has before simulation.
	 */
	BUCHI_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has before simulation.
	 */
	BUCHI_NONDETERMINISTIC_STATES,
	/**
	 * Amount of states the automaton has before simulation.
	 */
	BUCHI_STATES,
	/**
	 * The call transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded.
	 */
	BUCHI_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has before simulation multiplied
	 * with 1_000_000, then rounded.
	 */
	BUCHI_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded.
	 */
	BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has before simulation
	 * multiplied with 1_000_000, then rounded.
	 */
	BUCHI_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * Amount of transitions the automaton has before simulation.
	 */
	BUCHI_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has before simulation.
	 */
	BUCHI_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has before simulation.
	 */
	BUCHI_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has before simulation.
	 */
	BUCHI_TRANSITIONS_RETURN,
	/**
	 * The amount of states the determinized game automaton has.
	 */
	DETERMINIZED_GAME_AUTOMATON_STATES,
	/**
	 * Amount of merge attempts that where aborted.
	 */
	FAILED_MERGE_ATTEMPTS,
	/**
	 * Amount of transition removal attempts that where aborted.
	 */
	FAILED_TRANSREMOVE_ATTEMPTS,
	/**
	 * Amount of edges the game graph has.
	 */
	GAMEGRAPH_EDGES,
	/**
	 * Amount of vertices the game graph has.
	 */
	GAMEGRAPH_VERTICES,
	/**
	 * The global bound for infinty.
	 */
	GLOBAL_INFINITY,
	/**
	 * Amount of states a simulation has removed.
	 */
	REMOVED_STATES,
	/**
	 * Amount of transitions a simulation has removed.
	 */
	REMOVED_TRANSITIONS,
	/**
	 * Size of the alphabet the automaton has after simulation.
	 */
	RESULT_ALPHABET_SIZE,
	/**
	 * Size of the call alphabet the automaton has after simulation.
	 */
	RESULT_ALPHABET_SIZE_CALL,
	/**
	 * Size of the internal alphabet the automaton has after simulation.
	 */
	RESULT_ALPHABET_SIZE_INTERNAL,
	/**
	 * Size of the return alphabet the automaton has after simulation.
	 */
	RESULT_ALPHABET_SIZE_RETURN,
	/**
	 * Amount of nondeterministic states the automaton has after simulation.
	 */
	RESULT_NONDETERMINISTIC_STATES,
	/**
	 * Amount of states the automaton has after simulation.
	 */
	RESULT_STATES,
	/**
	 * The call transition density the automaton has after simulation multiplied
	 * with 1_000_000, then rounded.
	 */
	RESULT_TRANSITION_CALL_DENSITY_MILLION,
	/**
	 * The transition density the automaton has after simulation multiplied with
	 * 1_000_000, then rounded.
	 */
	RESULT_TRANSITION_DENSITY_MILLION,
	/**
	 * The internal transition density the automaton has after simulation
	 * multiplied with 1_000_000, then rounded.
	 */
	RESULT_TRANSITION_INTERNAL_DENSITY_MILLION,
	/**
	 * The return transition density the automaton has after simulation
	 * multiplied with 1_000_000, then rounded.
	 */
	RESULT_TRANSITION_RETURN_DENSITY_MILLION,
	/**
	 * Amount of transitions the automaton has after simulation.
	 */
	RESULT_TRANSITIONS,
	/**
	 * Amount of call transitions the automaton has after simulation.
	 */
	RESULT_TRANSITIONS_CALL,
	/**
	 * Amount of internal transitions the automaton has after simulation.
	 */
	RESULT_TRANSITIONS_INTERNAL,
	/**
	 * Amount of return transitions the automaton has after simulation.
	 */
	RESULT_TRANSITIONS_RETURN,
	/**
	 * Amount of SCCs the game graph has.
	 */
	SCCS,
	/**
	 * Amount of steps a simulation needed.
	 */
	SIMULATION_STEPS,
	/**
	 * Amount of sub-summarize edges a nwa game graph has.
	 */
	SUB_SUMMARIZE_EDGES,
	/**
	 * Amount of summarize edges a nwa game graph has.
	 */
	SUMMARIZE_EDGES
}
