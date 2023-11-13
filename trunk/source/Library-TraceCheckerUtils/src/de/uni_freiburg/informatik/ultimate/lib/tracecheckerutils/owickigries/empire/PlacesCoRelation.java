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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;

public final class PlacesCoRelation<PLACE, LETTER> {
	private final HashMap<PLACE, Set<PLACE>> mCoRelatedPlaces;
	private final ICoRelation<LETTER, PLACE> mCoRelation;

	/**
	 * 
	 * @param bp
	 *            Branching process for which the co-relation should be checked.
	 * @param net
	 *            Petri net corresponding to bp.
	 */
	public PlacesCoRelation(final BranchingProcess<LETTER, PLACE> bp, final IPetriNet<LETTER, PLACE> net) {
		mCoRelation = bp.getCoRelation();
		mCoRelatedPlaces = getAllCorelatedPlaces(net, bp);
	}

	private final HashMap<PLACE, Set<PLACE>> getAllCorelatedPlaces(final IPetriNet<LETTER, PLACE> net,
			BranchingProcess<LETTER, PLACE> bp) {
		Set<PLACE> originalPlaces = net.getPlaces();
		HashMap<PLACE, Set<PLACE>> coPlacesHashtable = new HashMap<>();
		for (PLACE place : originalPlaces) {
			Set<PLACE> coPlacesSet = new HashSet<>();
			for (PLACE place2 : originalPlaces) {
				if (!place.equals(place2) && placesCoRelation(place, place2, bp)) {
					coPlacesSet.add(place2);
				}
			}
			coPlacesHashtable.put(place, coPlacesSet);
		}
		return coPlacesHashtable;
	}

	private final boolean placesCoRelation(PLACE firstPlace, PLACE secondPlace, BranchingProcess<LETTER, PLACE> bp) {
		if (mCoRelatedPlaces.get(secondPlace).contains(firstPlace)) {
			return true;
		}
		Set<Condition<LETTER, PLACE>> firstPlaceConditions = bp.getConditions(firstPlace);
		Set<Condition<LETTER, PLACE>> secondPlaceConditions = bp.getConditions(secondPlace);
		for (Condition<LETTER, PLACE> condition1 : firstPlaceConditions) {
			for (Condition<LETTER, PLACE> condition2 : secondPlaceConditions) {
				if (!condition1.equals(condition2) && mCoRelation.isInCoRelation(condition1, condition2)) {
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
	public boolean getPlacesCorelation(PLACE firstPlace, PLACE secondPlace) {
		Set<PLACE> coPlacesSet = mCoRelatedPlaces.get(firstPlace);
		return coPlacesSet.contains(secondPlace);
	}
}
