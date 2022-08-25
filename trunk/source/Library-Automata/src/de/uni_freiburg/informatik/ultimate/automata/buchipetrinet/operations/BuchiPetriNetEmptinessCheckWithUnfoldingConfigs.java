package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

/*
 * TODO: If {@link BuchiPetriNetEmptinessCheckWithAccepts} is not much slower than this class, one could delete this
 * class. Although it is not yet optimized either.
 *
 * The method of looking for a lasso configuration in this class is essentially looking for a configuration in the
 * unfolding, which final state enables some maximum concurrent set of Events in that configuration such that the
 * created loop also contains an accepting place.
 *
 */
public class BuchiPetriNetEmptinessCheckWithUnfoldingConfigs<LETTER, PLACE> {
	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	Set<Event<LETTER, PLACE>> mUnfoldingEventsWithoutDummyRootEvent = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mAcceptingEvents = new HashSet<>();
	private final Set<Set<Event<LETTER, PLACE>>> mResultLassoConfigurations = new HashSet<>();
	private final Set<Set<Event<LETTER, PLACE>>> mConcurrentSubSets = new HashSet<>();

	private Set<PLACE> mMissingPlaces = new HashSet<>();

	private Event<LETTER, PLACE> mFoundationEvent = null;

	private final Set<Event<LETTER, PLACE>> mEndEvents = new HashSet<>();

	private final Set<Event<LETTER, PLACE>> mPossibleConfigEvents = new HashSet<>();

	private final Set<Event<LETTER, PLACE>> mAccptLoopEvents = new HashSet<>();

	/*
	 * (Terms used in the following reference the "An Improvement of McMillan's Unfolding Algorithm" - Esparza paper.)
	 *
	 * In essence this class searches for a configuration in Unfolding which' final state enables
	 */
	public BuchiPetriNetEmptinessCheckWithUnfoldingConfigs(final BranchingProcess<LETTER, PLACE> unfolding) {
		mUnfolding = unfolding;
		mMissingPlaces = null;
		mUnfoldingEventsWithoutDummyRootEvent =
				unfolding.getEvents().stream().filter(x -> x.getTransition() != null).collect(Collectors.toSet());
	}

	public final Set<Set<Event<LETTER, PLACE>>> getLassoConfigurations() {
		System.out.println(mResultLassoConfigurations);
		return mResultLassoConfigurations;
	}

	/*
	 * This method is (meant to be) called anytime the {@link BuchiPetriNetUnfolder} adds an event to the Unfolding. We
	 * then check if the prerequesites for a lasso configurations are met, and if so, compute if one exists.
	 */
	public final boolean update(final Event<LETTER, PLACE> event) {
		if (event.getTransition() == null) {
			return false;
		}
		for (final Event<LETTER, PLACE> childEvent : event.getLocalConfiguration()) {
			mEndEvents.remove(childEvent);
		}
		mEndEvents.add(event);
		mUnfoldingEventsWithoutDummyRootEvent.add(event);
		computeAcceptingEvents();
		return computeLassoConfigurations(event);

	}

	private final void computeAcceptingEvents() {
		for (final Condition<LETTER, PLACE> cond : mUnfolding.getAcceptingConditions()) {
			mAcceptingEvents.add(cond.getPredecessorEvent());
		}
	}

	private boolean computeLassoConfigurations(final Event<LETTER, PLACE> event) {
		for (final Event<LETTER, PLACE> accptLoopEvent : createsConfigurationWithHeadEvent(event)) {
			computeFoundation(accptLoopEvent);
		}
		return computeFoundation(event);
	}

	private boolean computeFoundation(final Event<LETTER, PLACE> event) {
		final Set<PLACE> finalState = new HashSet<>();
		finalState.addAll(event.getSuccessorConditions().stream().map(x -> x.getPlace()).collect(Collectors.toSet()));
		for (final Event<LETTER, PLACE> localEvent : event.getLocalConfiguration()) {
			final Set<PLACE> predecessorSet =
					localEvent.getPredecessorConditions().stream().map(x -> x.getPlace()).collect(Collectors.toSet());
			if (accptPlaceInLoop(localEvent) && localEvent.getPredecessorConditions().stream().map(x -> x.getPlace())
					.anyMatch(finalState::contains)) {
				mAccptLoopEvents.add(event);
				final Set<PLACE> missingPlaces = new HashSet<>(predecessorSet);
				missingPlaces.removeAll(finalState);
				mMissingPlaces = missingPlaces;
				mFoundationEvent = localEvent;
				if (computeMissingPartsOfLassoIfFoundation(event)) {
					System.out.println(mFoundationEvent);
					return true;
				}
			}
		}
		return false;
	}

	private Set<Event<LETTER, PLACE>> createsConfigurationWithHeadEvent(final Event<LETTER, PLACE> event) {
		final Set<Event<LETTER, PLACE>> accptLoopEventSet = new HashSet<>();
		for (final Event<LETTER, PLACE> accptLoopEvent : mAccptLoopEvents) {
			if (accptLoopEvent != event && mUnfolding.eventsInConcurrency(accptLoopEvent, event)) {
				accptLoopEventSet.add(accptLoopEvent);
			}
		}
		return accptLoopEventSet;
	}

	private boolean computeMissingPartsOfLassoIfFoundation(final Event<LETTER, PLACE> event) {

		final Set<Event<LETTER, PLACE>> loopHeadEventSet = new HashSet<>();
		for (final Event<LETTER, PLACE> localEvent : event.getLocalConfiguration()) {
			if (mUnfolding.eventsInConcurrency(localEvent, mFoundationEvent)) {
				loopHeadEventSet.add(localEvent);
			}
		}

		if (mMissingPlaces.size() == 0 && loopHeadEventSet.size() == 0) {
			final Set<Event<LETTER, PLACE>> singletonLassoConfig = new HashSet<>();
			singletonLassoConfig.add(event);
			mResultLassoConfigurations.add(singletonLassoConfig);
			return true;
		}

		mConcurrentSubSets.clear();
		for (final Event<LETTER, PLACE> headEvent : loopHeadEventSet) {
			final Set<Event<LETTER, PLACE>> concurrentSet = new HashSet<>();
			concurrentSet.add(event);
			concurrentSet.add(headEvent);
			mConcurrentSubSets.add(concurrentSet);
		}
		final Set<Event<LETTER, PLACE>> singleton = new HashSet<>();
		singleton.add(mFoundationEvent);
		mConcurrentSubSets.add(singleton);

		for (int i = 0; i < loopHeadEventSet.size(); i++) {
			final Set<Set<Event<LETTER, PLACE>>> setsToAddSet = new HashSet<>();
			final Set<Set<Event<LETTER, PLACE>>> setsToDeleteSet = new HashSet<>();
			for (final Event<LETTER, PLACE> headEvent : loopHeadEventSet) {
				for (final Set<Event<LETTER, PLACE>> set : mConcurrentSubSets) {
					if (fitsInEqualSet(headEvent, set)) {
						final Set<Event<LETTER, PLACE>> newSet = new HashSet<>();
						newSet.add(headEvent);
						newSet.addAll(set);
						setsToAddSet.add(newSet);
						setsToDeleteSet.add(set);
					}
				}
			}
			mConcurrentSubSets.removeAll(setsToDeleteSet);
			mConcurrentSubSets.addAll(setsToAddSet);
		}
		final Set<Set<PLACE>> mConcurrentSubSetsPredecessorSet = new HashSet<>();
		for (final Set<Event<LETTER, PLACE>> concSet : mConcurrentSubSets) {
			final Set<PLACE> predecessorPlaces = new HashSet<>();
			for (final Event<LETTER, PLACE> concEvent : concSet) {
				predecessorPlaces.addAll(concEvent.getPredecessorConditions().stream().map(x -> x.getPlace())
						.collect(Collectors.toSet()));
			}
			mConcurrentSubSetsPredecessorSet.add(predecessorPlaces);
		}

		mPossibleConfigEvents.clear();
		for (final Event<LETTER, PLACE> endEvent : mEndEvents) {
			if (mUnfolding.eventsInConcurrency(endEvent, event)) {
				if (endEvent.getSuccessorConditions().stream().map(x -> x.getPlace())
						.anyMatch(mMissingPlaces::contains)) {

					final Set<Event<LETTER, PLACE>> testSet = new HashSet<>();
					for (final Event<LETTER, PLACE> endEvent2 : mPossibleConfigEvents) {
						if (mUnfolding.eventsInConcurrency(endEvent, endEvent2)) {
							testSet.add(endEvent2);
						}
					}
					testSet.add(event);
					testSet.add(endEvent);
					final Set<PLACE> finalState = new HashSet<>();
					for (final Event<LETTER, PLACE> testEvent : testSet) {
						finalState.addAll(testEvent.getSuccessorConditions().stream().map(x -> x.getPlace())
								.collect(Collectors.toSet()));
					}
					for (final Set<PLACE> set : mConcurrentSubSetsPredecessorSet) {
						if (finalState.containsAll(set)) {
							mResultLassoConfigurations.add(testSet);
							return true;
						}
					}
					mPossibleConfigEvents.add(endEvent);
				}
			}
		}
		return false;
	}

	private boolean accptPlaceInLoop(final Event<LETTER, PLACE> loopHead) {
		for (final Event<LETTER, PLACE> accptEvent : mAcceptingEvents) {
			if (accptEvent.getLocalConfiguration().contains(loopHead)) {
				return true;
			}
		}
		return false;
	}

	private final boolean fitsInEqualSet(final Event<LETTER, PLACE> event,
			final Set<Event<LETTER, PLACE>> setofevents) {
		for (final Event<LETTER, PLACE> event2 : setofevents) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}
}
