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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.CoveringOptimizationVisitor.ICoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;

/**
 * A covering relation for automata created from one-safe Petri nets.
 *
 * A marking n is covered by a marking o if for all places p in n, either p is in o, or p has no successors and is not
 * accepting.
 *
 * This means that if e.g. one thread has reached a dead end location (e.g. an error location that is checked in another
 * CEGAR loop), then the resulting marking is covered by a marking where the thread is still running, and all other
 * threads are in the same location as before.
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
	private final Function<S, Marking<P>> mGetMarking;

	public Petri2AutomatonCoveringRelation(final IPetriNet<L, P> petriNet, final Function<S, Marking<P>> getMarking) {
		mPetriNet = petriNet;
		mGetMarking = Objects.requireNonNull(getMarking);
	}

	@Override
	public boolean covers(final S oldState, final S newState) {
		final Marking<P> oldMarking = mGetMarking.apply(oldState);
		final Marking<P> newMarking = mGetMarking.apply(newState);

		// TODO In the future, the second disjunct below could be replaced by a strictly weaker condition:
		// A (cached) check whether any accepting place can be reached from p.

		return newMarking.stream().allMatch(p -> oldMarking.contains(p) || (!canLeave(p) && !mPetriNet.isAccepting(p)));
	}

	private boolean canLeave(final P place) {
		return !mPetriNet.getSuccessors(place).isEmpty();
	}
}
