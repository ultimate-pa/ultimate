package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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
	private final Set<Event<LETTER, PLACE>> mConfigEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mLoopEvents = new HashSet<>();
	private List<PLACE> mMissinPlaces = new ArrayList<>();
	private List<PLACE> mSparePlaces = new ArrayList<>();

	private final void calcSpareMissingPlaces() {
		final List<PLACE> predSet = new ArrayList<>();
		final List<PLACE> succSet = new ArrayList<>();
		for (final Event<LETTER, PLACE> event : mLoopEvents) {
			predSet.addAll(event.getTransition().getPredecessors());
			succSet.addAll(event.getTransition().getSuccessors());
		}
		final List<PLACE> predSet2 = new ArrayList<>(predSet);
		predSet2.removeAll(succSet);
		setmMissinPlaces(predSet2);
		succSet.removeAll(predSet);
		setmSparePlaces(succSet);
	}

	public PotentialLassoConfiguration(final Event<LETTER, PLACE> loopEvent) {
		mConfigEvents.add(loopEvent);
		mLoopEvents.add(loopEvent);
		calcSpareMissingPlaces();
	}

	public PotentialLassoConfiguration(final Set<Event<LETTER, PLACE>> configEvents,
			final Set<Event<LETTER, PLACE>> loopEvents) {
		mConfigEvents.addAll(configEvents);
		mLoopEvents.addAll(loopEvents);
		calcSpareMissingPlaces();
	}

	public void addEvent(final Event<LETTER, PLACE> event) {
		mConfigEvents.add(event);
		calcSpareMissingPlaces();
	}

	public void addEvents(final Set<Event<LETTER, PLACE>> events) {
		mConfigEvents.addAll(events);
		calcSpareMissingPlaces();
	}

	public void addLoopEvent(final Event<LETTER, PLACE> event) {
		mConfigEvents.add(event);
		mLoopEvents.add(event);
		calcSpareMissingPlaces();
	}

	public PotentialLassoConfiguration<LETTER, PLACE> getCopy() {
		final PotentialLassoConfiguration<LETTER, PLACE> configuration =
				new PotentialLassoConfiguration<>(new HashSet<>(mConfigEvents), new HashSet<>(mLoopEvents));
		return configuration;
	}

	public Set<Event<LETTER, PLACE>> getConfigEvents() {
		return mConfigEvents;
	}

	public Set<Event<LETTER, PLACE>> getLoopEvents() {
		return mLoopEvents;
	}

	public List<PLACE> getmMissinPlaces() {
		return mMissinPlaces;
	}

	public void setmMissinPlaces(final List<PLACE> missinPlaces) {
		mMissinPlaces = missinPlaces;
	}

	public List<PLACE> getmSparePlaces() {
		return mSparePlaces;
	}

	public void setmSparePlaces(final List<PLACE> sparePlaces) {
		mSparePlaces = sparePlaces;
	}
}
