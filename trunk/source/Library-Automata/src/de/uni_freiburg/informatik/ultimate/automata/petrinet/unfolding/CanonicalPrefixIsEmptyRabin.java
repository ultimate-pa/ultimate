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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Checks if complete finite prefix contains accepting lasso configuration.
 *
 *
 */
public class CanonicalPrefixIsEmptyRabin<LETTER, PLACE> {
	BranchingProcess<LETTER, PLACE> mCompletePrefix;
	Set<Event<LETTER, PLACE>> mCutoffEventsWithDistantCompanion = new HashSet<>();
	Set<Event<LETTER, PLACE>> mLoopCutoffEvents = new HashSet<>();
	Set<Event<LETTER, PLACE>> mOriginLoopCutoffEvents = new HashSet<>();
	private PetriNetLassoRun<LETTER, PLACE> mRun = null;
	AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	Boolean searchAllLassoTypes = false;
	Set<Event<LETTER, PLACE>> mFiniteEvents = new HashSet<>();

	public CanonicalPrefixIsEmptyRabin(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> completePrefix) throws PetriNetNot1SafeException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mCompletePrefix = completePrefix;
		mLogger.info("Starting emptiness check.");
		for (final Event<LETTER, PLACE> event : mCompletePrefix.getEvents()) {
			for (final Condition<LETTER, PLACE> condition : event.getSuccessorConditions()) {
				if (((IRabinPetriNet<LETTER, PLACE>) mCompletePrefix.getNet()).isFinite(condition.getPlace())) {
					mFiniteEvents.add(event);
					continue;
				}
			}
		}
		classifyCutoffEvents();
		investigateCutOffs();
		mLogger.info("Finished emptiness check, language is " + (getResult() ? "empty" : "not empty"));
	}

	public PetriNetLassoRun<LETTER, PLACE> getLassoRun() {
		return mRun;
	}

	private boolean getResult() {
		return mRun == null;
	}

	private void classifyCutoffEvents() {
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
		investigateTypeOneLassos();

		// Type two lassos are already searched in PetrinetUnfolderBuchi.
		if (searchAllLassoTypes) {
			investigateTypeTwoLassos();
		}

		investigateTypeThreeLassos();
	}

	/**
	 * (edge case) Lasso word contained in local configuration where the stem-event of the Unfolding is an event
	 * companion.
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeOneLassos() throws PetriNetNot1SafeException {
		mLogger.info("Type 1 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mOriginLoopCutoffEvents) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				configLoopEvents.add(configEvent);
			}
			for (final Event<LETTER, PLACE> loopEvent : configLoopEvents) {
				for (final Condition<LETTER, PLACE> condition : loopEvent.getSuccessorConditions()) {
					if (((IRabinPetriNet<LETTER, PLACE>) mCompletePrefix.getNet()).isFinite(condition.getPlace())) {
						return;
					}
				}
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return;
			}
		}
		mLogger.info("Type 1 Lasso search ended.");
	}

	/**
	 * Lasso word contained in local configuration
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeTwoLassos() throws PetriNetNot1SafeException {
		mLogger.info("Type 2 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mLoopCutoffEvents) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}
			for (final Event<LETTER, PLACE> loopEvent : configLoopEvents) {
				for (final Condition<LETTER, PLACE> condition : loopEvent.getSuccessorConditions()) {
					if (((IRabinPetriNet<LETTER, PLACE>) mCompletePrefix.getNet()).isFinite(condition.getPlace())) {
						return;
					}
				}
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return;
			}
		}
		mLogger.info("Type 2 Lasso search ended.");
	}

	/**
	 * Lasso word contained in partial configuration. Finite places are dealt with in function
	 * fillReachableInformation().
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeThreeLassos() throws PetriNetNot1SafeException {
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
		final Map<Event<LETTER, PLACE>, Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>>> reachableCutoffsMapAccepting =
				new HashMap<>();
		for (final Event<LETTER, PLACE> accevent : acceptingEvents) {
			fillReachableInformation(accevent, needReachableInformationAcc, reachableCutoffsMapAccepting);
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
			final Map<Event<LETTER, PLACE>, Set<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>>> reachableCutoffsMap =
					new HashMap<>();
			fillReachableInformation(event, needReachableInformation, reachableCutoffsMap);
			if (reachableCutoffsMapAccepting.get(event.getCompanion()) == null
					|| reachableCutoffsMap.get(event.getCompanion()) == null) {
				continue;
			}

			// reachableCutoffsMapAccepting contains partial configurations of (event) companion and accepting
			// conditions,
			// reachableCutoffsMap contains partial configurations of accepting conditions and (event).
			// If the concatination of two such partial configurations is a valid partial configuration,
			// it contains a lasso word.
			for (final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair : reachableCutoffsMapAccepting
					.get(event.getCompanion())) {
				if (acceptingEvents.contains(pair.getFirst()) && reachableCutoffsMap.get(pair.getFirst()) != null) {
					for (final Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>> pair2 : reachableCutoffsMap
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
	 * Breadth first traversal of Unfolding, starting from (event) and going through every local configuration of cutoff
	 * events linked by their companion events that we find during traversal (recursively). We mark every event of
	 * interest, given with needReachableInformation, if it can build a partial configuration with (event). (in other
	 * words if the transition in the net reflected by (event) is reachable from the transition reflected by the event
	 * of interest, given the marking of the final state of the event of interest). The information for the described
	 * full partial configurations is stored in the map.
	 *
	 * If we encounter a finite place we dont traverse in that direction any further.
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
		final Set<Event<LETTER, PLACE>> finiteEventsInLocalConfig = new HashSet<>();
		for (final Event<LETTER, PLACE> finiteEvent : mFiniteEvents) {
			if (event.getLocalConfiguration().contains(finiteEvent)) {
				finiteEventsInLocalConfig.add(finiteEvent);
			}
		}
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

			if (!finiteEventsInLocalConfig.stream().allMatch(configEvent.getLocalConfiguration()::contains)
					|| finiteEventsInLocalConfig.contains(configEvent)) {
				continue;
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

			final Set<Event<LETTER, PLACE>> finiteEventsInLocalConfig2 = new HashSet<>();
			for (final Event<LETTER, PLACE> finiteEvent : mFiniteEvents) {
				if (currentEvent.getFirst().getLocalConfiguration().contains(finiteEvent)) {
					finiteEventsInLocalConfig2.add(finiteEvent);
				}
			}

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

				if (!finiteEventsInLocalConfig2.stream().allMatch(localConfigEvent.getLocalConfiguration()::contains)
						|| finiteEventsInLocalConfig2.contains(localConfigEvent)) {
					continue;
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
	 *            Constains all cutoff events from (event) companion to cutoff event containing accepting condition in
	 *            local config.
	 * @param pair2
	 *            Contains all cutoff events leading from (pair) cutoff events to (event) cutoff event.
	 * @return Boolean representing if given partial configuration contains accepting lasso word.
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

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final var buildAndCheck =
				new Events2PetriNetLassoRunBuchi<>(mServices, configLoopPart, configStemPart, mCompletePrefix);
		mRun = buildAndCheck.getLassoRun();
		return (mRun != null);
	}
}
