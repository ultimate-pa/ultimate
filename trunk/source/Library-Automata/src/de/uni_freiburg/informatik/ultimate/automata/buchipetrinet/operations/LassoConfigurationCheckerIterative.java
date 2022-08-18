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

	private Set<Event<LETTER, PLACE>> mSeenEvents = new HashSet<>();
	private Set<Event<LETTER, PLACE>> mNewEvents = new HashSet<>();

	private Set<Set<Event<LETTER, PLACE>>> mConcurrentSubSets = new HashSet<>();
	private Set<Set<Event<LETTER, PLACE>>> mCheckedConfigurations = new HashSet<>();
	private Set<Event<LETTER, PLACE>> mHeadEvents = new HashSet<>();

	private boolean mfindAllLassoMarkings;

	/*
	 * Computes the lasso configuration(s) of given Unfolding. The final state of a lasso configuration enables some
	 * concurrent set of events in its configuration. Any nodes of the configuration beyond that concurrent set of the
	 * configuration are the loop part of the lasso configuration and any nodes of the configuration before that
	 * concurrent set are the stem of the lasso configuration. There must be atleast one accepting place in the loop
	 * part of a lasso configuration.
	 * 
	 * A Buchipetri net accepts a word w iff there exists a lasso configuration in the Unfolding which includes w.
	 * 
	 */
	public LassoConfigurationCheckerIterative(BranchingProcess<LETTER, PLACE> unfolding, boolean findAllLassoMarkings) {
		mUnfolding = unfolding;
		mfindAllLassoMarkings = findAllLassoMarkings;
	}

	public final Set<Set<Event<LETTER, PLACE>>> getLassoConfigurations() {
		return mResultLassoConfigurations;
	}

	public final boolean update(BranchingProcess<LETTER, PLACE> unfolding) {
		// nur event
		//
		mUnfolding = unfolding;
		mUnfoldingEventsWithoutDummyRootEvent =
				unfolding.getEvents().stream().filter(x -> x.getTransition() != null).collect(Collectors.toSet());
		mNewEvents.addAll(mUnfoldingEventsWithoutDummyRootEvent);
		mNewEvents.removeAll(mSeenEvents);
		mSeenEvents.addAll(mUnfoldingEventsWithoutDummyRootEvent);
		mConcurrentSubSets.clear();
		return computeLassoConfigurations();
	}

	/*
	 * Anytime an event that fullfills the requirements of a new lasso configuration is added, we first check if its
	 * local configuration is a lasso configuration and then
	 */
	private final boolean computeLassoConfigurations() {
		computeAcceptingEvents();
		if (mAcceptingEvents.isEmpty()) {
			return false;
		}
		return checkEachNewEvent();
	}

	private final void computeAcceptingEvents() {
		for (Condition<LETTER, PLACE> cond : mUnfolding.getAcceptingConditions()) {
			mAcceptingEvents.add(cond.getPredecessorEvent());
		}
	}

	private boolean checkEachNewEvent() {
		boolean lassoFound = false;
		Set<Event<LETTER, PLACE>> reboundSet = new HashSet<>();
		Set<Event<LETTER, PLACE>> headEvents = new HashSet<>();
		// TODO: just check new one
		for (Event<LETTER, PLACE> event : mNewEvents) {
			if ((!localConfigContainsAcceptingPlace(event) || !localConfigContainsDoublePlace(event))) {
				if (!createsConfigurationWithHeadEvent(event).isEmpty()) {
					reboundSet.addAll(createsConfigurationWithHeadEvent(event));
				}
				continue;
			}
			headEvents.add(event);
			ArrayList<Event<LETTER, PLACE>> concurrentEventsOfNewEvent = new ArrayList<>();
			concurrentEventsOfNewEvent.add(event);

			lassoFound = fillPowerSetAndCheckForLasso(concurrentEventsOfNewEvent, event);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}

			for (Event<LETTER, PLACE> event2 : mUnfoldingEventsWithoutDummyRootEvent) {
				if (mUnfolding.eventsInConcurrency(event, event2)) {
					concurrentEventsOfNewEvent.add(event2);
				}
			}
			lassoFound = fillPowerSetAndCheckForLasso(concurrentEventsOfNewEvent, event);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}
		}
		mHeadEvents.addAll(headEvents);
		if (!reboundSet.isEmpty()) {
			mNewEvents.clear();
			mNewEvents.addAll(reboundSet);
			checkEachNewEvent();
		}
		return lassoFound;
	}

	private boolean localConfigContainsAcceptingPlace(Event<LETTER, PLACE> event) {
		return event.getLocalConfiguration().getEvents().stream().anyMatch(mAcceptingEvents::contains);
	}

	private boolean localConfigContainsDoublePlace(Event<LETTER, PLACE> event) {
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
		return false;
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
		// TODO: foreach
		for (int i = 0; i < concurrentEventsOfNewEvent.size(); i++) {
			Event<LETTER, PLACE> nextEvent = concurrentEventsOfNewEvent.get(i);
			fillConcurrentPowerset(mConcurrentSubSets, nextEvent);
			lassoFound = checkForLasso(event);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}
		}
		return lassoFound;
	}

	private final void fillConcurrentPowerset(Set<Set<Event<LETTER, PLACE>>> concurrentSubSets,
			Event<LETTER, PLACE> headEvent) {
		for (Event<LETTER, PLACE> event : headEvent.getLocalConfiguration().getEvents()) {
			Set<Set<Event<LETTER, PLACE>>> subSetUpdateSet = new HashSet<>();
			for (Set<Event<LETTER, PLACE>> set : concurrentSubSets) {
				if ((!set.contains(event)) && fitsInEqualSet(event, set)) {
					Set<Event<LETTER, PLACE>> newSubset = new HashSet<>();
					newSubset.add(event);
					newSubset.addAll(set);
					subSetUpdateSet.add(newSubset);
				}
			}
			concurrentSubSets.addAll(subSetUpdateSet);
			Set<Event<LETTER, PLACE>> singletonSet = new HashSet<>();
			singletonSet.add(event);
			concurrentSubSets.add(singletonSet);
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
			lassoFound = testConfiguration(configuration);
			if (lassoFound && !mfindAllLassoMarkings) {
				return true;
			}
			mCheckedConfigurations.add(configuration);
		}
		return lassoFound;
	}

	private final boolean testConfiguration(Set<Event<LETTER, PLACE>> configuration) {
		Set<PLACE> finalStateOfConfiguration = new HashSet<>();
		Set<Event<LETTER, PLACE>> configurationEvents = new HashSet<>();

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
