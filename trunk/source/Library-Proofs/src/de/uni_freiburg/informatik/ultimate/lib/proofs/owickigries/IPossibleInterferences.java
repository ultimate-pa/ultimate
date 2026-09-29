/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An interface that specifies the possible interferences in a model of a concurrent program. Specifically, a transition
 * of the program can <em>possibly interfere</em> with a program location if, while the program is in the given
 * location, some concurrent thread can execute the action.
 *
 * In general, an instance of this interface will present an overapproximation of the transitions that can actually be
 * executed concurrently. In particular, instances typically would track only what is possible up to control flow,
 * whereas data flow constraints would be ignored.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of transitions in the program model
 * @param <P>
 *            The type of program locations in the program model
 */
public interface IPossibleInterferences<T, P> {
	/**
	 * Retrieves the set of all transitions that possibly interfere with the given program location
	 *
	 * @param location
	 *            The program location whose possibly interfering transitions shall be retrieved
	 * @return a set containing all possibly interfering transitions
	 */
	Set<T> getInterferingActions(P location);

	/**
	 * Creates a new instance from the given data.
	 *
	 * @param <T>
	 *            The type of transitions in the program model
	 * @param <P>
	 *            The type of program locations in the program model
	 * @param rel
	 *            A binary relation from program locations to the possibly interfering transitions
	 * @return a new instance of the interface
	 */
	static <T, P> IPossibleInterferences<T, P> fromRelation(final HashRelation<P, T> rel) {
		return rel::getImage;
	}

	static <L, P> HashRelation<P, Transition<L, P>> fromUnfolding(final BranchingProcess<L, P> bp) {
		final HashRelation<P, Transition<L, P>> relation = new HashRelation<>();
		final ICoRelation<L, P> coRelation = bp.getCoRelation();
		for (final Condition<L, P> condition : bp.getConditions()) {
			final P place = condition.getPlace();
			for (final Event<L, P> event : coRelation.computeCoRelatatedEvents(condition)) {
				final Transition<L, P> transition = event.getTransition();
				if (!transition.getPredecessors().contains(place)) {
					relation.addPair(place, transition);
				}
			}
		}
		return relation;
	}
}
