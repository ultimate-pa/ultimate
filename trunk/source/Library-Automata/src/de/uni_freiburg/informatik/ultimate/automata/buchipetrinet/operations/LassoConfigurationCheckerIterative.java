package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public class LassoConfigurationCheckerIterative<LETTER, PLACE> {
	private BranchingProcess<LETTER, PLACE> mUnfolding;
	Set<Event<LETTER, PLACE>> mUnfoldingEventsWithoutDummyRootEvent;
	private Set<Event<LETTER, PLACE>> mAcceptingEvents = new HashSet<>();
	private Set<Set<Event<LETTER, PLACE>>> mResultLassoConfigurations = new HashSet<>();

	private Set<Set<Event<LETTER, PLACE>>> mConcurrentSubSets = new HashSet<>();
	private Set<Set<Event<LETTER, PLACE>>> mCheckedConfigurations = new HashSet<>();
	private Set<Event<LETTER, PLACE>> mHeadEvents = new HashSet<>();

	// Used for testing
	private boolean mfindAllLassoMarkings = false;

	/*
	 * (Terms used in the following reference the "An Improvement of McMillan's Unfolding Algorithm" - Esparza paper.)
	 * 
	 * Computes the lasso configuration(s) of given Unfolding. The final state of a lasso configuration enables some
	 * concurrent set of events in its configuration. Any nodes of the configuration beyond that concurrent set of the
	 * configuration are the loop part of the lasso configuration and any nodes of the configuration before that
	 * concurrent set are the stem of the lasso configuration. There must be atleast one accepting place in the loop
	 * part of a lasso configuration.
	 * 
	 * A Buchipetri net accepts a word w iff there exists a lasso configuration in the Unfolding which includes w.
	 */
	public LassoConfigurationCheckerIterative(BranchingProcess<LETTER, PLACE> unfolding) {
		mUnfolding = unfolding;
		mUnfoldingEventsWithoutDummyRootEvent =
				unfolding.getEvents().stream().filter(x -> x.getTransition() != null).collect(Collectors.toSet());
	}

	public final Set<Set<Event<LETTER, PLACE>>> getLassoConfigurations() {
		return mResultLassoConfigurations;
	}

	/*
	 * This method is (meant to be) called anytime the {@link BuchiPetriNetUnfolder} adds an event to the Unfolding. We
	 * then check if the prerequesites for a lasso configurations are met, and if so, compute if one exists.
	 */
	public final boolean update(Event<LETTER, PLACE> event) {
		if (event.getTransition() == null) {
			return false;
		}
		mUnfoldingEventsWithoutDummyRootEvent.add(event);
		return computeLassoConfigurations(event);
	}

	private final boolean computeLassoConfigurations(Event<LETTER, PLACE> event) {
		computeAcceptingEvents();
		return checkEvent(event);
	}

	private final void computeAcceptingEvents() {
		for (Condition<LETTER, PLACE> cond : mUnfolding.getAcceptingConditions()) {
			mAcceptingEvents.add(cond.getPredecessorEvent());
		}
	}

	private boolean checkEvent(Event<LETTER, PLACE> event) {
		boolean lassoFound = false;
		// requirements for a lasso configuration
		if ((!localConfigContainsAcceptingPlace(event) || !localConfigFinalStateContainsDuplicate(event))) {
			// if this event is concurrent to previous checked events which have the requirements to build a lasso
			// configuration, we must now check those events again with the new event(s) present, otherwise we might
			// miss a lasso configuration
			if (!createsConfigurationWithHeadEvent(event).isEmpty()) {
				for (Event<LETTER, PLACE> headEvent : createsConfigurationWithHeadEvent(event)) {
					checkEvent(headEvent);
				}
			}
			return false;
		}
		ArrayList<Event<LETTER, PLACE>> concurrentEventsOfNewEvent = new ArrayList<>();
		concurrentEventsOfNewEvent.add(event);

		// We do this call to try to make the common case faster, i.e. we test if the local configuration
		// of the event is a lasso configuration before searching concurrent head events and other configuration
		// combinations
		lassoFound = fillPowerSetAndCheckForLasso(concurrentEventsOfNewEvent, event);
		if (lassoFound && !mfindAllLassoMarkings) {
			return true;
		}

		for (Event<LETTER, PLACE> event2 : mUnfoldingEventsWithoutDummyRootEvent) {
			// Only events which local configs build loops can "help" our event to build a lasso configuration
			if (localConfigFinalStateContainsDuplicate(event2) && mUnfolding.eventsInConcurrency(event, event2)) {
				concurrentEventsOfNewEvent.add(event2);
			}
		}
		lassoFound = fillPowerSetAndCheckForLasso(concurrentEventsOfNewEvent, event);
		if (lassoFound && !mfindAllLassoMarkings) {
			return true;
		}

		mHeadEvents.add(event);
		return lassoFound;
	}

	private boolean localConfigContainsAcceptingPlace(Event<LETTER, PLACE> event) {
		return event.getLocalConfiguration().getEvents().stream().anyMatch(mAcceptingEvents::contains);
	}

	private boolean localConfigFinalStateContainsDuplicate(Event<LETTER, PLACE> event) {
		Set<PLACE> places = new HashSet<>();
		for (Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
			places.add(cond.getPlace());
		}
		for (Event<LETTER, PLACE> localEvent : event.getLocalConfiguration()) {
			if (localEvent == event) {
				continue;
			}
			for (Condition<LETTER, PLACE> condition : localEvent.getSuccessorConditions()) {
				if (places.contains(condition.getPlace())) {
					return true;
				}
			}
		}
		return mUnfolding.initialConditions().stream().anyMatch(places::contains);
	}

	private Set<Event<LETTER, PLACE>> createsConfigurationWithHeadEvent(Event<LETTER, PLACE> event) {
		Set<Event<LETTER, PLACE>> headEventSet = new HashSet<>();
		for (Event<LETTER, PLACE> headEvent : mHeadEvents) {
			if (mUnfolding.eventsInConcurrency(headEvent, event)) {
				headEventSet.add(headEvent);
			}
		}
		return headEventSet;
	}

	boolean fillPowerSetAndCheckForLasso(ArrayList<Event<LETTER, PLACE>> concurrentEventsOfNewEvent,
			Event<LETTER, PLACE> event) {
		boolean lassoFound = false;
		// Computes concurrent subsets of configuration, one of which successor Conditions have to be contained in the
		// final state of the configuration to make it a lasso configuration.
		// In each iteration we check for lasso in hopes to make the common case faster.
		for (Event<LETTER, PLACE> nextEvent : concurrentEventsOfNewEvent) {
			fillConcurrentPowerset(nextEvent);
			lassoFound = checkForLasso(event);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}
		}
		return lassoFound;
	}

	// Adds new concurrent subsets. These subsets are a subset of the powerset of all events which are concurrent to
	// eachother.
	private final void fillConcurrentPowerset(Event<LETTER, PLACE> headEvent) {
		for (Event<LETTER, PLACE> event : headEvent.getLocalConfiguration().getEvents()) {
			Set<Set<Event<LETTER, PLACE>>> subSetUpdateSet = new HashSet<>();
			for (Set<Event<LETTER, PLACE>> set : mConcurrentSubSets) {
				if ((!set.contains(event)) && fitsInEqualSet(event, set)) {
					Set<Event<LETTER, PLACE>> newSubset = new HashSet<>();
					newSubset.add(event);
					newSubset.addAll(set);
					subSetUpdateSet.add(newSubset);
				}
			}
			mConcurrentSubSets.addAll(subSetUpdateSet);
			Set<Event<LETTER, PLACE>> singletonSet = new HashSet<>();
			singletonSet.add(event);
			mConcurrentSubSets.add(singletonSet);
		}
	}

	private final boolean fitsInEqualSet(Event<LETTER, PLACE> event, Set<Event<LETTER, PLACE>> setofevents) {
		for (Event<LETTER, PLACE> event2 : setofevents) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	boolean checkForLasso(Event<LETTER, PLACE> event) {
		boolean lassoFound = false;
		for (Set<Event<LETTER, PLACE>> configuration : mConcurrentSubSets) {
			if (!configuration.contains(event) || mCheckedConfigurations.contains(configuration)) {
				continue;
			}
			lassoFound = isConfigurationLasso(configuration);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}
			mCheckedConfigurations.add(configuration);
		}
		return lassoFound;
	}

	private final boolean isConfigurationLasso(Set<Event<LETTER, PLACE>> configuration) {
		Set<PLACE> finalStateOfConfiguration = new HashSet<>();
		Set<Event<LETTER, PLACE>> configurationEvents = new HashSet<>();

		// compute finalStateOfConfiguration and configurationEvents
		for (Event<LETTER, PLACE> event : configuration) {
			configurationEvents.addAll(event.getLocalConfiguration().getEvents());
			for (Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
				finalStateOfConfiguration.add(cond.getPlace());
			}
		}

		for (Set<Event<LETTER, PLACE>> concurrentSet : mConcurrentSubSets) {
			if (!configurationEvents.containsAll(concurrentSet)) {
				continue;
			}
			Set<PLACE> markingofConcurrentSet = getMarkingOfSet(concurrentSet);
			if (finalStateOfConfiguration.containsAll(markingofConcurrentSet) && accptPlaceInLoop(concurrentSet)) {
				mResultLassoConfigurations.add(configuration);
				return true;
			}
		}
		return false;
	}

	private Set<PLACE> getMarkingOfSet(Set<Event<LETTER, PLACE>> concurrentSet) {
		Set<PLACE> markingofConcurrentSet = new HashSet<>();
		for (Event<LETTER, PLACE> event : concurrentSet) {
			for (Condition<LETTER, PLACE> condition : event.getPredecessorConditions()) {
				markingofConcurrentSet.add(condition.getPlace());
			}
		}
		return markingofConcurrentSet;
	}

	private boolean accptPlaceInLoop(Set<Event<LETTER, PLACE>> concurrentSet) {
		for (Event<LETTER, PLACE> accptEvent : mAcceptingEvents) {
			for (Event<LETTER, PLACE> event : concurrentSet) {
				if (accptEvent.getLocalConfiguration().contains(event)) {
					return true;
				}
			}
		}
		return false;
	}
}
