/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

/**
 * Interface for visitors used in DFS-based Partial Order Reductions on finite automata.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the finite automaton.
 * @param <S>
 *            The type of states in the automaton.
 */
public interface IPartialOrderVisitor<L, S> {
	/**
	 * Called when the DFS begins its search at an initial state of the automaton.
	 *
	 * @param state
	 *            initial state where the DFS starts
	 */
	void addStartState(S state);

	/**
	 * Called when a transition is discovered.
	 *
	 * @param source
	 *            source state of the discovered transition
	 * @param letter
	 *            letter of the discovered transition
	 * @param target
	 *            target of the discovered transition
	 * @return true to indicate that the discovered transition should be pruned, i.e., that the target state should not
	 *         be visited by the DFS (through this transition). Otherwise, return false.
	 */
	boolean discoverTransition(S source, L letter, S target);

	/**
	 * Called when a state is discovered.
	 *
	 * Note: At the moment, a state may be discovered and backtracked multiple times during the search.
	 *
	 * @param state
	 *            state that is discovered
	 * @return true to indicate that outgoing transitions of the state should be pruned, i.e., that the successor states
	 *         should not be visited by the DFS (from this state). Otherwise, return false.
	 */
	boolean discoverState(S state);

	/**
	 * Called when a state is backtracked.
	 *
	 * Note: A state may be discovered and backtracked multiple times during the search.
	 *
	 * @param state
	 *            state that is backtracked
	 */
	void backtrackState(S state);

	/**
	 * Called when a state is "delayed". This is specific to the "delay set" variant of Partial Order Reduction.
	 *
	 * @param state
	 *            state that is delayed
	 */
	// TODO (Dominik 2021-01-24) We should try to get rid of this method, as "delaying" states is an
	// implementation detail of SleepSetDelayReduction that should not be exposed to visitors.
	void delayState(S state);

	/**
	 * Used to indicate that the visitor is finished and further traversal of the automaton is not needed.
	 *
	 * @return true if the search should be (completely) aborted, false otherwise.
	 */
	boolean isFinished();
}
