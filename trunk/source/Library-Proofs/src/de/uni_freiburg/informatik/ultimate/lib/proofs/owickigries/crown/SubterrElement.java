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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown;

import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

class SubterrElement<LETTER, PLACE> {
	private final Marking<PLACE> mMarking;
	private final Set<Condition<LETTER, PLACE>> mCoSet;

	/**
	 * Element of a subterritory which holds a marking and the corresponding coset
	 *
	 * @param coSet
	 *            Coset of the subterritory
	 */
	public SubterrElement(final Set<Condition<LETTER, PLACE>> coSet) {
		mCoSet = coSet;
		mMarking = new Marking<>(calculateMarking());
	}

	private ImmutableSet<PLACE> calculateMarking() {
		return mCoSet.stream().map((Function<? super Condition<LETTER, PLACE>, ? extends PLACE>) Condition::getPlace).collect(ImmutableSet.collector());
	}

	public Marking<PLACE> getMarking() {
		return mMarking;
	}

	public Set<Condition<LETTER, PLACE>> getCoSet() {
		return mCoSet;
	}
}
