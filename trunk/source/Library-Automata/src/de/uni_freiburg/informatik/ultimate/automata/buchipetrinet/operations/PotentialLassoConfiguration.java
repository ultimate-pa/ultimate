package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public class PotentialLassoConfiguration<LETTER, PLACE> {
	private final Set<Event<LETTER, PLACE>> mEndEvents;

	public PotentialLassoConfiguration(final Set<Event<LETTER, PLACE>> endEvents) {
		mEndEvents = endEvents;
	}

	public void addEvent(final Event<LETTER, PLACE> event) {
		mEndEvents.add(event);
	}

	public PotentialLassoConfiguration<LETTER, PLACE> getCopy() {
		final PotentialLassoConfiguration<LETTER, PLACE> configuration = new PotentialLassoConfiguration<>(mEndEvents);
		return configuration;
	}

	public Set<Event<LETTER, PLACE>> getEndEvents() {
		return mEndEvents;
	}
}
