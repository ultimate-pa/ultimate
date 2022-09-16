package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract class for emptiness check that is executed within {@link PetriNetUnfolderInfinite}.
 *
 * @param <LETTER>
 *            letter type
 * @param <PLACE>
 *            place content type
 */
public abstract class UnfoldingInfiniteWordCheck<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	protected final BranchingProcess<LETTER, PLACE> mUnfolding;
	protected final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private final Set<PotentialLassoConfiguration<LETTER, PLACE>> mConcurrentEndEventPowerset = new HashSet<>();
	private final Set<PotentialLassoConfiguration<LETTER, PLACE>> mToBeExaminedConcurrentEndEvents = new HashSet<>();

	private final Set<Pair<NestedLassoWord<LETTER>, List<Event<LETTER, PLACE>>>> mResultLassoWordsWithConfigurations =
			new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mAcceptingEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mEndEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mLoopEvents = new HashSet<>();
	protected final Set<Event<LETTER, PLACE>> mAccptLoopEvents = new HashSet<>();
	protected final Map<Event<LETTER, PLACE>, Set<Event<LETTER, PLACE>>> mAccptLoopEventToLoopHeadMap = new HashMap<>();

	public UnfoldingInfiniteWordCheck(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> unfolding, final IPetriNetTransitionProvider<LETTER, PLACE> net) {
		super(services);
		mUnfolding = unfolding;
		mOperand = net;
	}

	@Override
	public Object getResult() {
		return (mResultLassoWordsWithConfigurations.size() > 0);
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	/**
	 * @return a Pair containing the lasso word and the lasso configuration.
	 */
	public final Pair<NestedLassoWord<LETTER>, List<Event<LETTER, PLACE>>> getLassoConfigurations() {
		return mResultLassoWordsWithConfigurations.iterator().next();
	}

	/**
	 * Supposed to be called by {@link BuchiPetriNetUnfolder} anytime an event is added to the Unfolding. Checks if
	 * Unfolding contains a lasso configuration, i.e. a configuration containing a word that is accepted by the origin
	 * BuchiPetriNet.
	 *
	 * @param <event>
	 *            The event added to the Unfolding
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
		computeIfLoopAndAccptLoopEvent(event);
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

	/**
	 * Updates mLoopEvents and mAccptLoopEvents which contains events which local configuration might contain a loop
	 * containing an accepting place.
	 */
	private boolean computeIfLoopAndAccptLoopEvent(final Event<LETTER, PLACE> event) {
		final Set<PLACE> finalState = new HashSet<>();
		finalState.addAll(event.getSuccessorConditions().stream().map(x -> x.getPlace()).collect(Collectors.toSet()));
		for (final Event<LETTER, PLACE> localEvent : event.getLocalConfiguration()) {
			if (localEvent.getPredecessorConditions().stream().map(x -> x.getPlace()).anyMatch(finalState::contains)) {
				mLoopEvents.add(event);
				final Set<Event<LETTER, PLACE>> headEvents = new HashSet<>();
				if (mAccptLoopEventToLoopHeadMap.get(event) != null) {
					headEvents.addAll(mAccptLoopEventToLoopHeadMap.get(event));
				}
				headEvents.add(localEvent);
				mAccptLoopEventToLoopHeadMap.put(event, headEvents);
				if (accptPlaceInLoop(localEvent)) {
					mAccptLoopEvents.add(event);
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

	/**
	 * We are looking for events which local configuration either is the foundation for a lasso configuration or
	 * combined with some other set of local configurations can build one. Thus whenever a new event is added we
	 * essentialy build the product set of this event and all potential lasso configuration event sets we have built
	 * before (mConcurrentEndEventPowerset), which are concurrent to this new event. We then check these new sets
	 * (mToBeExaminedConcurrentEndEvents) if one is a lasso configuration.
	 *
	 */
	private final void checkNewConfigurations(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		if (meetsConditionsToBeBaseOfLassoConfiguration(event)) {
			final Set<Event<LETTER, PLACE>> singletonSet = new HashSet<>();
			singletonSet.add(event);
			final PotentialLassoConfiguration<LETTER, PLACE> singleTonConfiguration =
					new PotentialLassoConfiguration<>(singletonSet);
			checkWordFromConfig(singleTonConfiguration);
			if (mResultLassoWordsWithConfigurations.size() > 0) {
				return;
			}
			mToBeExaminedConcurrentEndEvents.add(singleTonConfiguration);
		}
		// Non-loop events cannot help build a lasso configuration.
		if (!mLoopEvents.contains(event)) {
			return;
		}
		for (final PotentialLassoConfiguration<LETTER, PLACE> config : mConcurrentEndEventPowerset) {
			if (fitsInEqualSet(event, config.getEndEvents())) {

				final PotentialLassoConfiguration<LETTER, PLACE> newConfiguration = config.getCopy();

				newConfiguration.addEvent(event);

				mToBeExaminedConcurrentEndEvents.add(newConfiguration);
			}
		}
		for (final PotentialLassoConfiguration<LETTER, PLACE> configuration : mToBeExaminedConcurrentEndEvents) {
			checkWordFromConfig(configuration);
			if (mResultLassoWordsWithConfigurations.size() > 0) {
				return;
			}
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

	abstract boolean meetsConditionsToBeBaseOfLassoConfiguration(Event<LETTER, PLACE> event);

	abstract boolean extendsConfiguration(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config);

	/**
	 * Check if given configuration contains words that are accepted by the infinite petri net.
	 *
	 * @param configuration
	 * @throws PetriNetNot1SafeException
	 */
	private final void checkWordFromConfig(final PotentialLassoConfiguration<LETTER, PLACE> configuration)
			throws PetriNetNot1SafeException {
		final Set<Event<LETTER, PLACE>> allEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> headEvent : configuration.getEndEvents()) {
			for (final Event<LETTER, PLACE> configEvent : headEvent.getLocalConfiguration().getEvents()) {
				mAccptLoopEventToLoopHeadMap.put(configEvent, mAccptLoopEventToLoopHeadMap.get(headEvent));
				allEvents.add(configEvent);
			}
		}

		final List<Event<LETTER, PLACE>> configurationSorted = new ArrayList<>(allEvents);
		Collections.sort(configurationSorted, mUnfolding.getOrder());
		final NestedLassoWord<LETTER> lassoWord = getLassoWordFromConfiguration(configurationSorted);

		final BuchiAccepts<LETTER, PLACE> accepts = new BuchiAccepts<>(mServices, mOperand, lassoWord);
		if (accepts.getResult()) {
			mResultLassoWordsWithConfigurations.add(new Pair<>(lassoWord, configurationSorted));
		}
	}

	/**
	 * A configuration may contain multiple words, but since if one word is accepted by some BuchiPetriNet, all others
	 * of the configuration will be aswell, we only have to check one word from a configuration.
	 */
	private NestedLassoWord<LETTER>
			getLassoWordFromConfiguration(final List<Event<LETTER, PLACE>> configurationSorted) {
		final List<LETTER> stemLetters = new ArrayList<>();
		final List<LETTER> loopLetters = new ArrayList<>();
		for (final Event<LETTER, PLACE> event : configurationSorted) {
			boolean inLoop = false;
			for (final Event<LETTER, PLACE> headEvent : mAccptLoopEventToLoopHeadMap.get(event)) {
				if (event.getLocalConfiguration().getEvents().contains(headEvent)) {
					loopLetters.add(event.getTransition().getSymbol());
					inLoop = true;
					break;
				}
			}
			if (!inLoop) {
				stemLetters.add(event.getTransition().getSymbol());
			}

		}
		@SuppressWarnings("unchecked")
		final LETTER[] stem = (LETTER[]) stemLetters.toArray();
		final Word<LETTER> stemWord = new Word<>(stem);
		@SuppressWarnings("unchecked")
		final LETTER[] loop = (LETTER[]) loopLetters.toArray();
		final Word<LETTER> loopWord = new Word<>(loop);
		final NestedWord<LETTER> nestedstemWord = NestedWord.nestedWord(stemWord);
		final NestedWord<LETTER> nestedloopWord = NestedWord.nestedWord(loopWord);
		final NestedLassoWord<LETTER> lassoWord = new NestedLassoWord<>(nestedstemWord, nestedloopWord);
		return lassoWord;
	}
}
