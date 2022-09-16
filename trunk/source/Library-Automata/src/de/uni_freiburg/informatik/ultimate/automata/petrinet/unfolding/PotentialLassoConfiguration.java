package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Set;

/**
 * Set of events which local configurations in the unfolding build a configurations which might be a lasso
 * Configuration, i.e. a configuration which contains words accepted by the infinite petri net which the unfolding is
 * done on.
 *
 * @param <LETTER>
 * @param <PLACE>
 */
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
