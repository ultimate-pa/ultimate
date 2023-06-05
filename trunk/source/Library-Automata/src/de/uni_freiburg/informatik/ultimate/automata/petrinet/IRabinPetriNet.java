package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Set;

public interface IRabinPetriNet<LETTER, PLACE> extends IPetriNet<LETTER, PLACE> {
	Set<PLACE> getFinitePlaces();

	boolean isFinite(PLACE place);
}
