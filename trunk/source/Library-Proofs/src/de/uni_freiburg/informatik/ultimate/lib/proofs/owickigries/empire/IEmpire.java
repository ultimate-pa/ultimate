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

public interface IEmpire<L, P, S> extends INwaOutgoingLetterAndTransitionProvider<Transition<L, P>, S> {
	IPredicate getLaw(S state);

	Territory<P, Region<P>> getTerritory(S state);

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

	@Deprecated
	@Override
	default S getEmptyStackState() {
		// Empires do not support calls and returns.
		return null;
	}

	@Deprecated
	@Override
	default boolean isFinal(final S state) {
		// There is no meaningful notion of final states in empires.
		return false;
	}

	@Deprecated
	@Override
	default Iterable<OutgoingCallTransition<Transition<L, P>, S>> callSuccessors(final S state,
			final Transition<L, P> letter) {
		// Empires do not support calls and returns.
		return List.of();
	}

	@Deprecated
	@Override
	default Iterable<OutgoingReturnTransition<Transition<L, P>, S>> returnSuccessors(final S state, final S hier,
			final Transition<L, P> letter) {
		// Empires do not support calls and returns.
		return List.of();
	}
}
