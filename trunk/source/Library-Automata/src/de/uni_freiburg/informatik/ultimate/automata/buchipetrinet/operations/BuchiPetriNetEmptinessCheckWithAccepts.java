package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class BuchiPetriNetEmptinessCheckWithAccepts<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	private final IPetriNetTransitionProvider<LETTER, PLACE> mBuchiPetriNet;
	private final Set<Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>>> mConcurrentEndEventPowerset =
			new HashSet<>();
	private final Set<Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>>> mToBeExaminedConcurrentEndEvents =
			new HashSet<>();

	private final Set<Pair<NestedLassoWord<LETTER>, List<Event<LETTER, PLACE>>>> mResultLassoWordsWithConfigurations =
			new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mAcceptingEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mEndEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mLoopEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mAccptLoopEvents = new HashSet<>();
	private final Map<Event<LETTER, PLACE>, Event<LETTER, PLACE>> mAccptLoopEventToLoopHeadMap = new HashMap<>();

	public BuchiPetriNetEmptinessCheckWithAccepts(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> unfolding, final IPetriNetTransitionProvider<LETTER, PLACE> net) {
		super(services);
		mUnfolding = unfolding;
		mBuchiPetriNet = net;
	}

	@Override
	public Object getResult() {
		return (mResultLassoWordsWithConfigurations.size() > 0);
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, PLACE> getOperand() {
		return mBuchiPetriNet;
	}

	/*
	 * @return a Pair containing the lasso word and the lasso configuration.
	 */
	public final Set<Pair<NestedLassoWord<LETTER>, List<Event<LETTER, PLACE>>>> getLassoConfigurations() {
		System.out.println(mResultLassoWordsWithConfigurations);
		return mResultLassoWordsWithConfigurations;
	}

	/*
	 * Supposed to be called by {@link BuchiPetriNetUnfolder} anytime an event is added to the Unfolding. Checks if
	 * Unfolding contains a lasso configuration, i.e. a configuration containing a word that is accepted by the origin
	 * BuchiPetriNet.
	 *
	 * @param <event> The event added to the Unfolding
	 *
	 * @return boolean representing if lasso configuration was found.
	 *
	 */
	public final boolean update(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		// skipping artificial root event of Branchingprocess
		if (event.getTransition() == null) {
			return false;
		}
		for (final Event<LETTER, PLACE> childEvent : event.getLocalConfiguration()) {
			mEndEvents.remove(childEvent);
		}
		mEndEvents.add(event);
		computeIfAcceptingEvent(event);
		computeIfAccptLoopEvent(event);
		checkNewConfigurations(event);
		if (mResultLassoWordsWithConfigurations.size() > 0) {
			return true;
		}
		return false;
	}

	private final void computeIfAcceptingEvent(final Event<LETTER, PLACE> event) {
		if (event.getSuccessorConditions().stream().anyMatch(mUnfolding.getAcceptingConditions()::contains)) {
			mAcceptingEvents.add(event);
		}
	}

	/*
	 * Updates mAccptLoopEvents which contains events which local configuration might contain a loop containing an
	 * accepting place.
	 */
	private boolean computeIfAccptLoopEvent(final Event<LETTER, PLACE> event) {
		final Set<PLACE> finalState = new HashSet<>();
		finalState.addAll(event.getSuccessorConditions().stream().map(x -> x.getPlace()).collect(Collectors.toSet()));
		for (final Event<LETTER, PLACE> localEvent : event.getLocalConfiguration()) {
			if (localEvent.getPredecessorConditions().stream().map(x -> x.getPlace()).anyMatch(finalState::contains)) {
				mLoopEvents.add(event);
				if (accptPlaceInLoop(localEvent)) {
					mAccptLoopEvents.add(event);
					mAccptLoopEventToLoopHeadMap.put(event, localEvent);
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

	/*
	 * We are looking for events which local configuration either is the foundation for a lasso configuration or
	 * combined with some other set of local configurations can build one. Thus whenever a new event is added we
	 * essentialy build the product set of this event and all potential lasso configuration event sets we have built
	 * before (mConcurrentEndEventPowerset). We then check these new sets (mToBeExaminedConcurrentEndEvents) if one is a
	 * lasso configuration.
	 *
	 * (The sets of events are the "Headevents" which combined local configurations is the configuration we are
	 * testing.)
	 */
	private final void checkNewConfigurations(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		if (mAccptLoopEvents.contains(event)) {
			final Set<Event<LETTER, PLACE>> singletonSet = new HashSet<>();
			singletonSet.add(event);
			final Event<LETTER, PLACE> loopHead = mAccptLoopEventToLoopHeadMap.get(event);
			final Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> singletonPair =
					new Pair<>(singletonSet, loopHead);
			mToBeExaminedConcurrentEndEvents.add(singletonPair);
		}
		// non loop events cannot help build a lasso configuration
		if (!mLoopEvents.contains(event)) {
			return;
		}
		for (final Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> pair : mConcurrentEndEventPowerset) {
			if (fitsInEqualSet(event, pair.getFirst())) {
				final Set<Event<LETTER, PLACE>> newConcSubSet = new HashSet<>();
				newConcSubSet.add(event);
				newConcSubSet.addAll(pair.getFirst());
				final Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> newPair =
						new Pair<>(newConcSubSet, pair.getSecond());
				mToBeExaminedConcurrentEndEvents.add(newPair);
			}
		}
		for (final Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> configurationHeads : mToBeExaminedConcurrentEndEvents) {
			checkWordFromConfigHeads(configurationHeads);
		}
		mConcurrentEndEventPowerset.addAll(mToBeExaminedConcurrentEndEvents);
		mToBeExaminedConcurrentEndEvents.clear();
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

	private final void
			checkWordFromConfigHeads(final Pair<Set<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> configurationEnd)
					throws PetriNetNot1SafeException {
		final Set<Event<LETTER, PLACE>> allEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> headEvent : configurationEnd.getFirst()) {
			allEvents.addAll(headEvent.getLocalConfiguration().getEvents());
		}
		final List<Event<LETTER, PLACE>> configurationSorted = new ArrayList<>(allEvents);
		Collections.sort(configurationSorted, new EventComparator());
		final NestedLassoWord<LETTER> lassoWord =
				getLassoWordFromConfiguration(configurationSorted, configurationEnd.getSecond());

		final BuchiPetrinetAccepts<LETTER, PLACE> accepts =
				new BuchiPetrinetAccepts<>(mServices, mBuchiPetriNet, lassoWord);
		if (accepts.getResult()) {
			mResultLassoWordsWithConfigurations.add(new Pair<>(lassoWord, configurationSorted));
		}
	}

	/*
	 * A configuration may contain multiple words, but since if one word is accepted by some BuchiPetriNet, all others
	 * of the configuration will be aswell, we only have to check one word from a configuration.
	 */
	private NestedLassoWord<LETTER> getLassoWordFromConfiguration(final List<Event<LETTER, PLACE>> configurationSorted,
			final Event<LETTER, PLACE> loopHead) {
		final List<LETTER> stemLetters = new ArrayList<>();
		final List<LETTER> loopLetters = new ArrayList<>();
		boolean inLoop = false;
		for (final Event<LETTER, PLACE> event : configurationSorted) {
			if (event == loopHead) {
				inLoop = true;
			}
			if (!inLoop) {
				stemLetters.add(event.getTransition().getSymbol());
			} else {
				loopLetters.add(event.getTransition().getSymbol());
			}
		}
		final LETTER[] stem = (LETTER[]) stemLetters.toArray();
		final Word<LETTER> stemWord = new Word<>(stem);
		final LETTER[] loop = (LETTER[]) loopLetters.toArray();
		final Word<LETTER> loopWord = new Word<>(loop);
		final NestedWord<LETTER> nestedstemWord = NestedWord.nestedWord(stemWord);
		final NestedWord<LETTER> nestedloopWord = NestedWord.nestedWord(loopWord);
		final NestedLassoWord<LETTER> lassoWord = new NestedLassoWord<>(nestedstemWord, nestedloopWord);
		return lassoWord;
	}

	/*
	 * Helper class to compare events within a configuration.
	 */
	class EventComparator implements Comparator<Event<LETTER, PLACE>> {
		@Override
		public int compare(final Event<LETTER, PLACE> e1, final Event<LETTER, PLACE> e2) {
			if (mUnfolding.eventsInConcurrency(e1, e2)) {
				return 0;
			}
			return e1.getDepth() - e2.getDepth();
		}
	}
}
