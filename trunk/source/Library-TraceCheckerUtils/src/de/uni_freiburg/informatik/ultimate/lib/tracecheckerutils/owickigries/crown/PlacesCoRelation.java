/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

final class PlacesCoRelation<PLACE, LETTER> {
	private final HashRelation<PLACE, PLACE> mCoRelatedPlaces;
	private final ICoRelation<LETTER, PLACE> mCoRelation;

	/**
	 * Store the pairwise corelation for all original Places of bp.
	 *
	 * @param bp
	 *            Branching process for which the co-relation should be checked.
	 * @param net
	 *            Original Petri net.
	 */
	public PlacesCoRelation(final BranchingProcess<LETTER, PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mCoRelatedPlaces = getAllCorelatedPlaces(bp);
	}

	private final HashRelation<PLACE, PLACE> getAllCorelatedPlaces(final BranchingProcess<LETTER, PLACE> bp) {
		final List<PLACE> places =
				bp.getConditions().stream().map(condition -> condition.getPlace()).collect(Collectors.toList());
		final HashRelation<PLACE, PLACE> coPlacesHashtable = new HashRelation<>();
		for (int i = 0; i < places.size(); i++) {
			for (int j = i; j < places.size(); j++) {
				final PLACE place1 = places.get(i);
				final PLACE place2 = places.get(j);
				if (!place1.equals(place2) && placesCoRelation(place1, place2, bp)) {
					coPlacesHashtable.addPair(place1, place2);
					coPlacesHashtable.addPair(place2, place1);
				}
			}
		}
		return coPlacesHashtable;
	}

	private final boolean placesCoRelation(final PLACE firstPlace, final PLACE secondPlace,
			final BranchingProcess<LETTER, PLACE> bp) {
		if (firstPlace.equals(secondPlace)) {
			return false;
		}
		final Set<Condition<LETTER, PLACE>> firstPlaceConditions = bp.getConditions(firstPlace);
		final Set<Condition<LETTER, PLACE>> secondPlaceConditions = bp.getConditions(secondPlace);
		for (final Condition<LETTER, PLACE> condition1 : firstPlaceConditions) {
			for (final Condition<LETTER, PLACE> condition2 : secondPlaceConditions) {
				if (mCoRelation.isInCoRelation(condition1, condition2)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks co-relation for two places.
	 *
	 * @param firstPlace
	 *            First Place for co-relation check.
	 * @param secondPlace
	 *            Second Place for co-relation check.
	 * @return true if the places are co-related else false.
	 */
	public boolean getPlacesCorelation(final PLACE firstPlace, final PLACE secondPlace) {
		return mCoRelatedPlaces.containsPair(firstPlace, secondPlace);
	}
}
