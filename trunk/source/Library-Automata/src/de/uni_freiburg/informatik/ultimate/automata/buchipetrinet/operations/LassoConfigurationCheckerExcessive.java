package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

// TODO: delete or optimize this class
// WARNING: insanely unoptimized class just for testing, use LassoConfigurationCheckerIterative instead
public class LassoConfigurationCheckerExcessive<LETTER, PLACE> {
	private Set<HashSet<Event<LETTER, PLACE>>> mConcurrentEvents;
	private BranchingProcess<LETTER, PLACE> mUnfolding;
	private Set<Event<LETTER, PLACE>> mAcceptingEvents;
	private Set<Set<Event<LETTER, PLACE>>> mResultLassoConfigurations = new HashSet<>();

	public LassoConfigurationCheckerExcessive(BranchingProcess<LETTER, PLACE> unfolding) {
		mUnfolding = unfolding;
		mConcurrentEvents = new HashSet<>();
		mAcceptingEvents = new HashSet<>();
		computeLassoCOnfigurations();
	}

	public final Set<Set<Event<LETTER, PLACE>>> getLassoConfigurations() {
		return mResultLassoConfigurations;
	}

	private final void computeLassoCOnfigurations() {
		computeAcceptingEvents();
		if (mAcceptingEvents.isEmpty()) {
			return;
		}
		mConcurrentEvents = getConcurrentEvents();
		checkAllConfigurations();
	}

	private final void computeAcceptingEvents() {
		Set<Condition<LETTER, PLACE>> accptConditions =
				(Set<Condition<LETTER, PLACE>>) mUnfolding.getAcceptingConditions();
		for (Condition<LETTER, PLACE> cond : accptConditions) {
			mAcceptingEvents.add(cond.getPredecessorEvent());
		}
	}

	private Set<HashSet<Event<LETTER, PLACE>>> getConcurrentEvents() {
		Set<HashSet<Event<LETTER, PLACE>>> equalunfoldingEventss = new HashSet<>();
		Set<Event<LETTER, PLACE>> unfoldingEvents = (Set<Event<LETTER, PLACE>>) mUnfolding.getEvents();
		for (Event<LETTER, PLACE> event : unfoldingEvents) {
			if (event.getPredecessorConditions().toArray().length == 0) {
				continue;
			}
			HashSet<Event<LETTER, PLACE>> hashSet = new HashSet<>();
			hashSet.add(event);
			equalunfoldingEventss.add(hashSet);
		}
		for (int i = 0; i < unfoldingEvents.toArray().length + 1; i++) {
			Set<HashSet<Event<LETTER, PLACE>>> unfoldingEventssResult = new HashSet<>();
			for (Event<LETTER, PLACE> event : unfoldingEvents) {
				if (event.getPredecessorConditions().toArray().length == 0) {
					continue;
				}
				for (HashSet<Event<LETTER, PLACE>> hashSet2 : equalunfoldingEventss) {
					if (fitsInEqualSet(event, hashSet2)) {
						HashSet<Event<LETTER, PLACE>> hashSet = new HashSet<>();
						hashSet.add(event);
						hashSet.addAll(hashSet2);
						unfoldingEventssResult.add(hashSet);
					}
				}
			}
			equalunfoldingEventss.addAll(unfoldingEventssResult);
		}
		return equalunfoldingEventss;
	}

	private final boolean fitsInEqualSet(Event<LETTER, PLACE> event, Set<Event<LETTER, PLACE>> setofevents) {
		for (Event<LETTER, PLACE> event2 : setofevents) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	private final void checkAllConfigurations() {
		for (Set<Event<LETTER, PLACE>> configuration : mConcurrentEvents) {

			Set<PLACE> finalStateOfConfiguration = new HashSet<>();
			Set<Event<LETTER, PLACE>> configurationEvents = new HashSet<>();
			for (Event<LETTER, PLACE> event : configuration) {
				configurationEvents.addAll(event.getLocalConfiguration().getEvents());
				for (Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
					finalStateOfConfiguration.add(cond.getPlace());
				}
			}

			Set<Set<Event<LETTER, PLACE>>> concurrentSetsOfConfiguration = new HashSet<>();
			for (Set<Event<LETTER, PLACE>> eventSet : mConcurrentEvents) {
				if (configurationEvents.containsAll(eventSet)) {
					concurrentSetsOfConfiguration.add(eventSet);
				}
			}
			for (Set<Event<LETTER, PLACE>> concurrentSet : concurrentSetsOfConfiguration) {
				Set<PLACE> markingofConcurrentSet = new HashSet<>();
				for (Event<LETTER, PLACE> event : concurrentSet) {
					for (Condition<LETTER, PLACE> condition : event.getPredecessorConditions()) {
						markingofConcurrentSet.add(condition.getPlace());
					}
				}

				if (finalStateOfConfiguration.containsAll(markingofConcurrentSet)) {
					for (Event<LETTER, PLACE> accptEvent : mAcceptingEvents) {
						for (Event<LETTER, PLACE> event : concurrentSet) {
							if (accptEvent.getLocalConfiguration().contains(event)) {
								mResultLassoConfigurations.add(configuration);
							}
						}
					}
				}
			}
		}
	}
}
