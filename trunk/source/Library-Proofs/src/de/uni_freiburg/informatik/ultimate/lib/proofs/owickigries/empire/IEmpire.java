/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Represents an empire (automaton), as defined in our POPL'26 paper
 *
 * The Ghosts of Empires: Extracting Modularity from Interleaving-Based Proofs. Schüssele, Zumkeller, Lagunes-Rochin and
 * Klumpp, POPL'26
 *
 * A valid empire represents a correctness proof of a Petri program. It maps abstractions of the history (the
 * interleaving executed so far), represented by the automaton states, to assertions about the data state (represented
 * as predicates) and control configuration (represented by {@link Territory} instances) reached after such a history.
 *
 * @param <L>
 *            The type of letters in the empire resp. the proven Petri program
 * @param <P>
 *            The type of places in the proven Petri program
 * @param <S>
 *            The type of states in the empire
 */
public interface IEmpire<L, P, S> extends INwaOutgoingLetterAndTransitionProvider<Transition<L, P>, S> {
	/**
	 * Maps an empire state to its "law", i.e., the corresponding data assertion
	 */
	IPredicate getLaw(S state);

	/**
	 * Maps an empire state to its "territory", which describes possible control configurations
	 */
	Territory<P, Region<P>> getTerritory(S state);

	/**
	 * Convenience method: Determines if the given state's territory contains the given place.
	 */
	default boolean containsPlace(final S state, final P place) {
		// Convenience method.
		return getTerritory(state).containsPlace(place);
	}

	@Deprecated
	@Override
	default IStateFactory<S> getStateFactory() {
		// This method is deprecated and should not be used.
		return null;
	}

	/**
	 * Empires do not support calls and returns.
	 */
	@Deprecated
	@Override
	default S getEmptyStackState() {
		return null;
	}

	/**
	 * There is no meaningful notion of final states in empires.
	 */
	@Deprecated
	@Override
	default boolean isFinal(final S state) {
		return false;
	}

	/**
	 * Empires do not support calls and returns.
	 */
	@Deprecated
	@Override
	default Iterable<OutgoingCallTransition<Transition<L, P>, S>> callSuccessors(final S state,
			final Transition<L, P> letter) {
		return List.of();
	}

	/**
	 * Empires do not support calls and returns.
	 */
	@Deprecated
	@Override
	default Iterable<OutgoingReturnTransition<Transition<L, P>, S>> returnSuccessors(final S state, final S hier,
			final Transition<L, P> letter) {
		return List.of();
	}
}
