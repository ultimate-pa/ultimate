package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public class PotentialLassoConfiguration<LETTER, PLACE> {
	private final Set<Event<LETTER, PLACE>> mEndEvents;
	private final Event<LETTER, PLACE> mLoopheadEvent;
	private final Set<PLACE> mNeededPlacesForLoopHead;
	private final Set<PLACE> mCurrentContainedPlaces;

	public PotentialLassoConfiguration(final Set<Event<LETTER, PLACE>> endEvents, final Event<LETTER, PLACE> loopHead) {
		mEndEvents = endEvents;
		mLoopheadEvent = loopHead;
		mNeededPlacesForLoopHead = getNeededPlacesForLoopHead();
		mCurrentContainedPlaces = getCurrentContainedPlaces();
	}

	public void addPlaces(final Set<PLACE> places) {
		mCurrentContainedPlaces.addAll(places);
	}

	public void addEvent(final Event<LETTER, PLACE> event) {
		mEndEvents.add(event);
	}

	public PotentialLassoConfiguration<LETTER, PLACE> getCopy() {
		final PotentialLassoConfiguration<LETTER, PLACE> configuration =
				new PotentialLassoConfiguration<>(mEndEvents, mLoopheadEvent);
		return configuration;
	}

	public boolean isLassoConfiguration() {
		return mCurrentContainedPlaces.containsAll(mNeededPlacesForLoopHead);
	}

	public Event<LETTER, PLACE> getLoopheadEvent() {
		return mLoopheadEvent;
	}

	public Set<Event<LETTER, PLACE>> getEndEvents() {
		return mEndEvents;
	}

	private Set<PLACE> getNeededPlacesForLoopHead() {
		final Set<PLACE> neededPlaces = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : mLoopheadEvent.getPredecessorConditions()) {
			neededPlaces.add(condition.getPlace());
		}
		return neededPlaces;
	}

	private Set<PLACE> getCurrentContainedPlaces() {
		final Set<PLACE> currentPlaces = new HashSet<>();
		for (final Event<LETTER, PLACE> event : mEndEvents) {
			for (final Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
				currentPlaces.add(cond.getPlace());
			}
		}
		return currentPlaces;
	}

	public final boolean extendsConfiguration(final Event<LETTER, PLACE> event) {
		if (!event.getLocalConfiguration().contains(mLoopheadEvent)) {
			return false;
		}

		final Set<PLACE> newPlaceSet = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
			newPlaceSet.add(cond.getPlace());
		}
		if (mCurrentContainedPlaces.containsAll(newPlaceSet)) {
			return false;
		}
		return true;
	}
}
