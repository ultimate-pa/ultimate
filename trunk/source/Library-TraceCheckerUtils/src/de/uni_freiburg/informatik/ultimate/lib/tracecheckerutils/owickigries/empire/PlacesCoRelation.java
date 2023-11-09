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
