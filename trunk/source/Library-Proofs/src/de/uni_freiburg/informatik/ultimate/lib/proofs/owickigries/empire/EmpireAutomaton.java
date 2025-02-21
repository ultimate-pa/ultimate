/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Matthias Zumkeller
 * Copyright (C) 2024 University of Freiburg
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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class EmpireAutomaton<L, P> implements IEmpireAutomaton<L, P, EmpireAutomaton.State<L, P>> {
	@Override
	public IPredicate getLaw(final State<L, P> state) {
		return state.law();
	}

	@Override
	public boolean containsPlace(final State<L, P> state, final P place) {
		return state.territory().getPlaces().contains(place);
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<State<L, P>> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(final State<L, P> state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "unknown";
	}

	@Override
	public Set<Transition<L, P>> lettersInternal(final State<L, P> state) {
		// TODO Consider whether we can efficiently override this method
		return IEmpireAutomaton.super.lettersInternal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, State<L, P>>>
			internalSuccessors(final State<L, P> state, final Transition<L, P> letter) {

		// (state is marked)

		// step 1: see if letter should lead to any successor at all or can be optimized away
		// (iterate over alphabet and see which other transitions are enabled in the territory)
		final boolean canBePruned = false;
		if (canBePruned) {
			return List.of();
		}

		// step 2: compute the "direct" successor state for the given transition

		// step 3: while the current successor is not marked, pick one (or a set of) transitions and compute the
		// successor again

		// step 4: from the maximal successor, create a State record
		final State<L, P> successor = null;

		// return the edge to the maximal successor
		return List.of(new OutgoingInternalTransition<>(letter, successor));
	}

	public record State<L, P>(Territory<P> territory, IPredicate law, Set<Region<P>> bystanders) {
		// empty body
	}
}
