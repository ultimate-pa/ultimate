/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
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

import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class PetriOwickiGries {
	public static final boolean IGNORE_CUTOFF_CONDITIONS = true;

	public static final boolean isCutoff(final Condition<?, ?> cond) {
		return cond.getPredecessorEvent().isCutoffEvent();
	}

	public static <L, P> IPossibleInterferences<Transition<L, P>, P> getPossibleInterferences(
			final BranchingProcess<L, P> bp, final Set<P> originalPlaces,
			final Function<Transition<L, P>, Transition<L, P>> diff2OriginalTransition) {
		final HashRelation<P, Transition<L, P>> relation = new HashRelation<>();
		final ICoRelation<L, P> coRelation = bp.getCoRelation();

		for (final Condition<L, P> condition : bp.getConditions()) {
			final P place = condition.getPlace();
			if (!originalPlaces.contains(place)) {
				continue;
			}
			for (final Event<L, P> event : coRelation.computeCoRelatatedEvents(condition)) {
				final Transition<L, P> transition = event.getTransition();
				if (!transition.getPredecessors().contains(place)) {
					final var originalTransition = diff2OriginalTransition.apply(transition);
					assert originalTransition != null : "no original transition for " + transition;
					relation.addPair(place, originalTransition);
				}
			}
		}
		return IPossibleInterferences.fromRelation(relation);
	}
}
