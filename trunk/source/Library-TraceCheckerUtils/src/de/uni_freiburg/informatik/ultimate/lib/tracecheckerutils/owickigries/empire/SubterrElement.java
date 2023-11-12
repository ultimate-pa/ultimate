package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

public class SubterrElement<LETTER, PLACE> {
	Set<PLACE> mMarking;
	Set<Condition<LETTER, PLACE>> mCoSet;

	public SubterrElement(Set<Condition<LETTER, PLACE>> coSet) {
		mCoSet = coSet;
		mMarking = calculateMarking();
	}

	private Set<PLACE> calculateMarking() {
		Set<PLACE> marking = new HashSet<>();
		for (Condition<LETTER, PLACE> condition : mCoSet) {
			marking.add(condition.getPlace());
		}
		return marking;
	}

	public Set<PLACE> getMarking() {
		return mMarking;
	}

	public Set<Condition<LETTER, PLACE>> getCoSet() {
		return mCoSet;
	}
}
