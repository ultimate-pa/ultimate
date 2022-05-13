/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.ICoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;

/**
 * A covering relation for automata created from one-safe Petri nets.
 *
 * @see de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.LazyPetriNet2FiniteAutomaton
 * @see de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the finite automaton
 * @param <P>
 *            The type of places
 */
public class Petri2AutomatonCoveringRelation<L, S, P> implements ICoveringRelation<S> {
	private final IPetriNet<L, P> mPetriNet;
	private final Function<S, Marking<L, P>> mGetMarking;

	public Petri2AutomatonCoveringRelation(final IPetriNet<L, P> petriNet,
			final Function<S, Marking<L, P>> getMarking) {
		mPetriNet = petriNet;
		mGetMarking = Objects.requireNonNull(getMarking);
	}

	@Override
	public boolean covers(final S oldState, final S newState) {
		final Marking<L, P> oldMarking = mGetMarking.apply(oldState);
		final Marking<L, P> newMarking = mGetMarking.apply(newState);

		final boolean oldAccepting = mPetriNet.isAccepting(oldMarking);

		for (final P place : newMarking) {
			if (oldMarking.contains(place)) {
				// Places that are themselves contained in oldMarking are represented.
				continue;
			}
			if (canLeave(place)) {
				// A place that has outgoing transitions (but is not itself in oldMarking) breaks covering.
				return false;
			}
			if (!oldAccepting && mPetriNet.isAccepting(place)) {
				// An accepting marking cannot be covered by a non-accepting marking.
				return false;
			}
		}

		return true;
	}

	private boolean canLeave(final P place) {
		return !mPetriNet.getSuccessors(place).isEmpty();
	}
}
