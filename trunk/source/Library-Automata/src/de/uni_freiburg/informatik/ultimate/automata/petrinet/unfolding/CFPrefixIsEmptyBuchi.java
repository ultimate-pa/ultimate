package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Checks if complete finite prefix contains accepting lasso configuration.
 *
 */
public class CFPrefixIsEmptyBuchi<LETTER, PLACE> {
	BranchingProcess<LETTER, PLACE> mCompletePrefix;
	Set<Event<LETTER, PLACE>> mCutoffEventsWithDistantCompanion = new HashSet<>();
	Set<Event<LETTER, PLACE>> mLoopCutoffEvents = new HashSet<>();
	Set<Event<LETTER, PLACE>> mOriginLoopCutoffEvents = new HashSet<>();
	private PetriNetLassoRun<LETTER, PLACE> mRun = null;
	AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	private Map<Event<LETTER, PLACE>, Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>>> mReachableCutoffsMapAccepting;
	private Map<Event<LETTER, PLACE>, Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>>> mReachableCutoffsMap;

	public CFPrefixIsEmptyBuchi(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> completePrefix) throws PetriNetNot1SafeException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mCompletePrefix = completePrefix;
		mLogger.info("Starting emptiness check.");
		search();
		investigateCutOffs();
		mLogger.info("Finished emptiness check, language is " + (getResult() ? "empty" : "not empty"));
	}

	public PetriNetLassoRun<LETTER, PLACE> getLassoRun() {
		return mRun;
	}

	private boolean getResult() {
		return mRun == null;
	}

	private void search() {
		mLogger.info("Starting cutoff event analysis.");
		for (final Event<LETTER, PLACE> event : mCompletePrefix.getCutoffEvents()) {
			if (event.getLocalConfiguration().contains(event.getCompanion())) {
				mLoopCutoffEvents.add(event);
			} else if (event.getCompanion().getTransition() == null) {
				mOriginLoopCutoffEvents.add(event);
			} else {
				mCutoffEventsWithDistantCompanion.add(event);
			}
		}
		mLogger.info("Ended cutoff event analysis.");
	}

	private void investigateCutOffs() throws PetriNetNot1SafeException {
		// Type 1 lassos are edge cases where the stem-event of the Unfolding is an event companion
		mLogger.info("Type 1 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mOriginLoopCutoffEvents) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				configLoopEvents.add(configEvent);
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return;
			}
		}
		mLogger.info("Type 1 Lasso search ended.");

		mLogger.info("Type 3 Lasso search started.");
		// First denote for all companion events of the cutoff events we investigate, if they can even reach an
		// accepting event.
		final Set<Event<LETTER, PLACE>> acceptingEvents = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : mCompletePrefix.getAcceptingConditions()) {
			acceptingEvents.add(condition.getPredecessorEvent());
		}
		final Set<Event<LETTER, PLACE>> needReachableInformationAcc = new HashSet<>(acceptingEvents);
		for (final Event<LETTER, PLACE> event : mCutoffEventsWithDistantCompanion) {
			needReachableInformationAcc.add(event.getCompanion());
		}
		mReachableCutoffsMapAccepting = new HashMap<>();
		for (final Event<LETTER, PLACE> accevent : acceptingEvents) {
			fillReachableInformation(accevent, needReachableInformationAcc, mReachableCutoffsMapAccepting);
		}

		// For every cutoff event check if its companion event can reach an accepting event and then the cutoff event
		// itself.
		// If that is the case, that partial configuration contains an accepting word.
		int cutoffCounter = 0;
		for (final Event<LETTER, PLACE> event : mCutoffEventsWithDistantCompanion) {
			cutoffCounter += 1;
			mLogger.info("Checking partial configuations of cutoff event " + cutoffCounter + " / "
					+ mCutoffEventsWithDistantCompanion.size());

			final Set<Event<LETTER, PLACE>> needReachableInformation = new HashSet<>(acceptingEvents);
			needReachableInformation.add(event.getCompanion());
			mReachableCutoffsMap = new HashMap<>();
			fillReachableInformation(event, needReachableInformation, mReachableCutoffsMap);
			if (mReachableCutoffsMapAccepting.get(event.getCompanion()) == null
					|| mReachableCutoffsMap.get(event.getCompanion()) == null) {
				continue;
			}

			for (final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair : mReachableCutoffsMapAccepting
					.get(event.getCompanion())) {
				if (acceptingEvents.contains(pair.getFirst()) && mReachableCutoffsMap.get(pair.getFirst()) != null) {
					for (final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair2 : mReachableCutoffsMap
							.get(pair.getFirst())) {
						if (pair2.getFirst() == event && pair.getSecond().containsAll(pair2.getSecond())) {
							if (buildAndCheckPartialConfig(event, pair, pair2)) {
								return;
							}
						}
					}
				}
			}
		}
		mLogger.info("Type 3 Lasso search ended.");
	}

	/**
	 * Breadth first traversal of Unfolding, starting from (event) and going through every local configuration linked by
	 * cuttoff events and their companion events. We mark every event of interest, given with needReachableInformation,
	 * if it can build a partial configuration with (event). (in other words if the transition in the net reflected by
	 * (event) is reachable from the transition reflected by the event of interest, given the marking of the final state
	 * of the event of interest).
	 *
	 * Stack used to simulate recursive tree traversal.
	 *
	 * @param event
	 * @param needReachableInformation
	 * @param reachableMap
	 */
	private void fillReachableInformation(final Event<LETTER, PLACE> event,
			final Set<Event<LETTER, PLACE>> needReachableInformation,
			final Map<Event<LETTER, PLACE>, Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>>> reachableMap) {
		final Deque<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>> functionStack = new ArrayDeque<>();
		final Set<Event<LETTER, PLACE>> alreadySeenEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()) {
			if (!(configEvent == event) && needReachableInformation.contains(configEvent)) {
				if (reachableMap.get(configEvent) != null) {
					final var newSet = reachableMap.get(configEvent);
					newSet.add(new Pair<>(event, new ArrayList<>()));
					reachableMap.put(configEvent, newSet);
				} else {
					final Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>> singleton = new HashSet<>();
					singleton.add(new Pair<>(event, new ArrayList<>()));
					reachableMap.put(configEvent, singleton);
				}
			}

			if (configEvent.isCompanion()) {
				alreadySeenEvents.add(configEvent);
				for (final Event<LETTER, PLACE> cutoffevent : configEvent.getCutoffEventsThisIsCompanionTo()) {
					final List<Event<LETTER, PLACE>> cutoffs = new ArrayList<>();
					cutoffs.add(cutoffevent);
					functionStack.push(new Pair<>(cutoffevent, cutoffs));
				}
			}
		}

		while (!functionStack.isEmpty()) {
			final var currentEvent = functionStack.pop();
			alreadySeenEvents.add(currentEvent.getFirst());
			for (final Event<LETTER, PLACE> localConfigEvent : currentEvent.getFirst().getLocalConfiguration()) {
				if (needReachableInformation.contains(localConfigEvent)) {
					if (reachableMap.get(localConfigEvent) != null) {
						final var newSet = reachableMap.get(localConfigEvent);
						newSet.add(new Pair<>(event, currentEvent.getSecond()));
						reachableMap.put(localConfigEvent, newSet);
					} else {
						final Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>> singleton = new HashSet<>();
						singleton.add(new Pair<>(event, currentEvent.getSecond()));
						reachableMap.put(localConfigEvent, singleton);
					}
				}
				if (localConfigEvent.isCompanion()) {
					for (final Event<LETTER, PLACE> cutoffevent : localConfigEvent.getCutoffEventsThisIsCompanionTo()) {
						if (!alreadySeenEvents.contains(cutoffevent)) {
							final List<Event<LETTER, PLACE>> cutoffs = new ArrayList<>(currentEvent.getSecond());
							cutoffs.add(cutoffevent);
							functionStack.push(new Pair<>(cutoffevent, cutoffs));
						}
					}
				}
			}
		}
	}

	/**
	 * Hacky way to build the partial config given the result of a type 3 lasso off investigateCutOffs.
	 *
	 * @param event
	 * @param pair
	 * @param pair2
	 * @return
	 * @throws PetriNetNot1SafeException
	 */
	private boolean buildAndCheckPartialConfig(final Event<LETTER, PLACE> event,
			final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair,
			final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair2) throws PetriNetNot1SafeException {
		final List<Event<LETTER, PLACE>> stemEvents = new ArrayList<>();
		final List<Event<LETTER, PLACE>> loopEvents = new ArrayList<>();
		Event<LETTER, PLACE> currentCompanionEvent = event.getCompanion();
		for (int i = pair.getSecond().size() - 1; i >= 0; i--) {
			if (i == pair.getSecond().size() - 1) {
				for (final Event<LETTER, PLACE> configEvent : pair.getSecond().get(i).getLocalConfiguration()
						.getSortedConfiguration(mCompletePrefix.getOrder())) {
					if (configEvent.getLocalConfiguration().contains(currentCompanionEvent)
							&& configEvent != currentCompanionEvent) {
						loopEvents.add(configEvent);
					} else {
						stemEvents.add(configEvent);
					}

				}
			} else {
				for (final Event<LETTER, PLACE> configEvent : pair.getSecond().get(i).getLocalConfiguration()
						.getSortedConfiguration(mCompletePrefix.getOrder())) {
					if (configEvent.getLocalConfiguration().contains(currentCompanionEvent)
							&& configEvent != currentCompanionEvent) {
						loopEvents.add(configEvent);
					}
				}
			}
			currentCompanionEvent = pair.getSecond().get(i).getCompanion();
		}
		for (int i = pair2.getSecond().size() - 1; i >= 0; i--) {
			for (final Event<LETTER, PLACE> configEvent : pair2.getSecond().get(i).getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				if (configEvent.getLocalConfiguration().contains(currentCompanionEvent)
						&& configEvent != currentCompanionEvent) {
					loopEvents.add(configEvent);
				}
			}
			currentCompanionEvent = pair2.getSecond().get(i).getCompanion();
		}
		for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
				.getSortedConfiguration(mCompletePrefix.getOrder())) {
			if (configEvent.getLocalConfiguration().contains(currentCompanionEvent)
					&& configEvent != currentCompanionEvent) {
				loopEvents.add(configEvent);
			}
		}
		if (checkIfLassoConfigurationAccepted(loopEvents, stemEvents)) {
			return true;
		}
		return false;
	}

	/**
	 * Given loop and stem events we build a {@link PetriNetLassoRun}.
	 *
	 * @param configLoopPart
	 * @param configStemPart
	 * @return
	 * @throws PetriNetNot1SafeException
	 */
	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final List<Transition<LETTER, PLACE>> stemTransitions = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> loopTransitions = new ArrayList<>();

		boolean acceptingPlaceShotintoInLoop = false;
		for (final Event<LETTER, PLACE> loopEvent : configLoopPart) {
			if (loopEvent.getTransition().getSuccessors().stream().anyMatch(mCompletePrefix.getNet()::isAccepting)) {
				acceptingPlaceShotintoInLoop = true;
			}
			loopTransitions.add(loopEvent.getTransition());
		}
		if (!acceptingPlaceShotintoInLoop) {
			return false;
		}

		for (final Event<LETTER, PLACE> stemEvent : configStemPart) {
			stemTransitions.add(stemEvent.getTransition());
		}

		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mCompletePrefix.getNet().getInitialPlaces()));

		final var pair = constructFeasibleLetterAndMarkingSequence(startMarking, stemTransitions);
		if (pair == null) {
			return false;
		}
		final List<LETTER> stemLetters = pair.getFirst();
		final List<Marking<PLACE>> sequenceOfStemMarkings = pair.getSecond();

		final var pair2 = constructFeasibleLetterAndMarkingSequence(
				sequenceOfStemMarkings.get(sequenceOfStemMarkings.size() - 1), loopTransitions);
		if (pair2 == null) {
			return false;
		}
		final List<LETTER> loopLetters = pair2.getFirst();
		final List<Marking<PLACE>> sequenceOfLassoMarkings = pair2.getSecond();

		return createAndCheckLassoRun(stemLetters, sequenceOfStemMarkings, loopLetters, sequenceOfLassoMarkings);
	}

	private final Pair<List<LETTER>, List<Marking<PLACE>>> constructFeasibleLetterAndMarkingSequence(
			Marking<PLACE> startMarking, final List<Transition<LETTER, PLACE>> loopTransitions)
			throws PetriNetNot1SafeException {
		// TODO: Check this method for theroetical correctness
		// Since some number of events might be in concurrency the sorting might have not returned the correct
		// order of events. We thus juggle non enabled events in this stack always trying if they are enabled
		// in the next iteration.
		final List<LETTER> loopLetters = new ArrayList<>();
		final List<Marking<PLACE>> sequenceOfLassoMarkings = new ArrayList<>();
		final Deque<Transition<LETTER, PLACE>> waitingLoopTransitionStack = new ArrayDeque<>();
		sequenceOfLassoMarkings.add(startMarking);
		for (final Transition<LETTER, PLACE> transition : loopTransitions) {
			for (int i = 0; i < waitingLoopTransitionStack.size(); i++) {
				final var waitingTransition = waitingLoopTransitionStack.pop();
				if (startMarking.isTransitionEnabled(waitingTransition)) {
					loopLetters.add(waitingTransition.getSymbol());
					startMarking = startMarking.fireTransition(waitingTransition);
					sequenceOfLassoMarkings.add(startMarking);
				} else {
					waitingLoopTransitionStack.addFirst(transition);
				}
			}

			if (!startMarking.isTransitionEnabled(transition)) {
				waitingLoopTransitionStack.push(transition);
				continue;
			}
			loopLetters.add(transition.getSymbol());
			startMarking = startMarking.fireTransition(transition);
			sequenceOfLassoMarkings.add(startMarking);
		}

		return new Pair<>(loopLetters, sequenceOfLassoMarkings);
	}

	private final boolean createAndCheckLassoRun(final List<LETTER> stemLetters,
			final List<Marking<PLACE>> sequenceOfStemMarkings, final List<LETTER> loopLetters,
			final List<Marking<PLACE>> sequenceOfLassoMarkings) throws PetriNetNot1SafeException {
		@SuppressWarnings("unchecked")
		final LETTER[] stem = (LETTER[]) stemLetters.toArray();
		final Word<LETTER> stemWord = new Word<>(stem);
		@SuppressWarnings("unchecked")
		final LETTER[] loop = (LETTER[]) loopLetters.toArray();
		final Word<LETTER> loopWord = new Word<>(loop);

		final NestedWord<LETTER> nestedstemWord = NestedWord.nestedWord(stemWord);
		final NestedWord<LETTER> nestedloopWord = NestedWord.nestedWord(loopWord);

		final NestedLassoWord<LETTER> nestedLassoWord = new NestedLassoWord<>(nestedstemWord, nestedloopWord);
		final PetriNetRun<LETTER, PLACE> stemRun = new PetriNetRun<>(sequenceOfStemMarkings, nestedstemWord);
		final PetriNetRun<LETTER, PLACE> loopRun = new PetriNetRun<>(sequenceOfLassoMarkings, nestedloopWord);
		final PetriNetLassoRun<LETTER, PLACE> lassoRun = new PetriNetLassoRun<>(stemRun, loopRun);
		// this BuchiAccepts should not be needed, but acts as a last correctness check for unknown edge cases
		final BuchiAccepts<LETTER, PLACE> accepts = new BuchiAccepts<>(mServices,
				(IPetriNetTransitionProvider<LETTER, PLACE>) mCompletePrefix.getNet(), nestedLassoWord);
		final boolean accpted = accepts.getResult();
		if (accpted) {
			mRun = lassoRun;
			return true;
		}
		return false;
	}
}
