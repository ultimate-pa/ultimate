/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Interface describing minimal operation set of Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter
 * @param <STATE>
 *            state
 */
public interface IRabinAutomaton<LETTER, STATE> extends IAutomaton<LETTER, STATE> {
	/**
	 * @return All initial states of the automaton.
	 */
	Set<STATE> getInitialStates();

	/**
	 * checks if state is initial
	 *
	 * @param state
	 *            state
	 * @return true iff the state is initial.
	 */
	default boolean isInitial(final STATE state) {
		return getInitialStates().contains(state);
	}

	/**
	 * checks if state is accepting
	 *
	 * @param state
	 *            state
	 * @return true iff the state is accepting.
	 */
	boolean isAccepting(STATE state);

	/**
	 * checks if state is finite
	 *
	 * @param state
	 *            state
	 * @return true iff the state is finite. (Should only be visited finitely often.)
	 */
	boolean isFinite(STATE state);

	/**
	 * All successor transitions for a given state.
	 *
	 * @param state
	 *            state
	 * @return outgoing transitions all possible outgoing transitions for this state
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state);

	/**
	 * Successor transitions for a given state and letter pair.
	 *
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return resulting outgoing transitions for these parameters
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter);

	@Override
	default IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException("Rabin automata are not yet implemented as Ultimate model.");
	}
}
