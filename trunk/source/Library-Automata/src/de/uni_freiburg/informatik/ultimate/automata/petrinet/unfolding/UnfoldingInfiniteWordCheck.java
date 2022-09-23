package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
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
	private final Set<Event<LETTER, PLACE>> mAcceptingEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mEndEvents = new HashSet<>();
	private final Set<Event<LETTER, PLACE>> mLoopEvents = new HashSet<>();
	protected final Set<Event<LETTER, PLACE>> mAccptLoopEvents = new HashSet<>();
	protected final Map<Event<LETTER, PLACE>, Set<Event<LETTER, PLACE>>> mAccptLoopEventToLoopHeadMap = new HashMap<>();
	public final Set<FireSequenceInProgress<LETTER, PLACE>> mResultPairReal = new HashSet<>();
	public PetriNetLassoRun<LETTER, PLACE> mRun = null;

	private final Map<Transition<LETTER, PLACE>, Set<Event<LETTER, PLACE>>> mTransitionToAllPredecessorsMap =
			new HashMap<>();

	private final Set<Pair<Set<Event<LETTER, PLACE>>, Set<PLACE>>> mConcurrentlyReachablePlaceSetsPairs =
			new HashSet<>();

	private final Map<Transition<LETTER, PLACE>, Set<Set<Event<LETTER, PLACE>>>> mTransitionToAllLocalConfigsMap =
			new HashMap<>();

	public UnfoldingInfiniteWordCheck(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> unfolding, final IPetriNetTransitionProvider<LETTER, PLACE> net) {
		super(services);
		mUnfolding = unfolding;
		mOperand = net;
	}

	@Override
	public Object getResult() {
		return false;
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	/**
	 * @return a Pair containing the lasso word and the lasso configuration.
	 */
	public final Pair<NestedLassoWord<LETTER>, List<Event<LETTER, PLACE>>> getLassoConfigurations() {
		return null;// mResultLassoWordsWithConfigurations.iterator().next();
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
	 * @throws PetriNetNot1SafeException
	 * @throws AutomataLibraryException
	 *
	 */
	public final boolean update(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		// skipping artificial root event of Branchingprocess
		if (event.getTransition() == null) {
			return false;
		}
		fillLocalConfigMap(event);
		fillConcurrentPlaceSet(event);
		fillPredecessorMap(event);
		for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
			mEndEvents.remove(event2);
		}
		mEndEvents.add(event);
		computeIfAcceptingEvent(event);
		computeIfLoopAndAccptLoopEvent(event);
		checkNewConfigurations(event);
		if (mRun != null) {
			return true;
		}
		return false;
	}

	private final void fillLocalConfigMap(final Event<LETTER, PLACE> event) {
		final Set<Set<Event<LETTER, PLACE>>> localConfigSets = new HashSet<>();
		final Set<Event<LETTER, PLACE>> localconfigSet = new HashSet<>();
		localconfigSet.addAll(event.getLocalConfiguration().getEvents());
		if (mTransitionToAllLocalConfigsMap.get(event.getTransition()) != null) {
			localConfigSets.addAll(mTransitionToAllLocalConfigsMap.get(event.getTransition()));
		}
		localConfigSets.add(localconfigSet);
		mTransitionToAllLocalConfigsMap.put(event.getTransition(), localConfigSets);
	}

	private final void fillConcurrentPlaceSet(final Event<LETTER, PLACE> event) {
		final Set<PLACE> succSet = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : event.getSuccessorConditions()) {
			succSet.add(condition.getPlace());
		}
		final Set<Event<LETTER, PLACE>> singletonEvent = new HashSet<>();
		singletonEvent.add(event);
		mConcurrentlyReachablePlaceSetsPairs.add(new Pair<>(singletonEvent, succSet));
		for (final Pair<Set<Event<LETTER, PLACE>>, Set<PLACE>> pair : mConcurrentlyReachablePlaceSetsPairs) {
			if (fitsInEqualSet2(event, pair.getFirst())) {
				pair.getFirst().add(event);
				for (final Condition<LETTER, PLACE> condition : event.getSuccessorConditions()) {
					pair.getSecond().add(condition.getPlace());
				}

			}
		}
	}

	private final void fillPredecessorMap(final Event<LETTER, PLACE> event) {
		final Set<Event<LETTER, PLACE>> oldEvents = new HashSet<>();
		if (mTransitionToAllPredecessorsMap.get(event.getTransition()) != null) {
			oldEvents.addAll(mTransitionToAllPredecessorsMap.get(event.getTransition()));
		}
		for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration().getEvents()) {
			oldEvents.add(event2);
			if (mTransitionToAllPredecessorsMap.get(event2.getTransition()) != null) {
				for (final Event<LETTER, PLACE> event3 : mTransitionToAllPredecessorsMap.get(event2.getTransition())) {
					oldEvents.add(event3);
				}
			}
		}
		mTransitionToAllPredecessorsMap.put(event.getTransition(), oldEvents);
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
	 * @throws PetriNetNot1SafeException
	 *
	 * @throws AutomataLibraryException
	 *
	 */
	private final void checkNewConfigurations(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		if (meetsConditionsToBeBaseOfLassoConfiguration(event)) {
			for (final Event<LETTER, PLACE> event3 : mAccptLoopEventToLoopHeadMap.get(event)) {
				final Set<Event<LETTER, PLACE>> singletonSet = new HashSet<>();
				for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
					if (event2.getLocalConfiguration().contains(event3) && event2 != event) {
						singletonSet.add(event2);
					}
				}
				final PotentialLassoConfiguration<LETTER, PLACE> singleTonConfiguration =
						new PotentialLassoConfiguration<>(event);
				singleTonConfiguration.addEvents(singletonSet);
				mToBeExaminedConcurrentEndEvents.add(singleTonConfiguration);
			}
			final Set<PotentialLassoConfiguration<LETTER, PLACE>> otherLassosConfigurations =
					getNeighbourPotentialLassos(event);
			mToBeExaminedConcurrentEndEvents.addAll(otherLassosConfigurations);

		}
		// Non-loop events cannot help build a lasso configuration.
		if (!mLoopEvents.contains(event)) {
			return;
		}
		for (final PotentialLassoConfiguration<LETTER, PLACE> config : mConcurrentEndEventPowerset) {
			if (fitsInEqualSet(event, config)) {

				for (final Event<LETTER, PLACE> event3 : mAccptLoopEventToLoopHeadMap.get(event)) {
					final PotentialLassoConfiguration<LETTER, PLACE> newConfiguration = config.getCopy();
					for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
						if (event2.getLocalConfiguration().contains(event3)) {
							newConfiguration.addEvent(event2);
						}
					}
					newConfiguration.addLoopEvent(event);
					mToBeExaminedConcurrentEndEvents.add(newConfiguration);
				}

				final Set<PotentialLassoConfiguration<LETTER, PLACE>> otherLassosConfigurations =
						getNeighbourPotentialLassos(event);
				for (final PotentialLassoConfiguration<LETTER, PLACE> potentialLassoConfiguration : otherLassosConfigurations) {
					final PotentialLassoConfiguration<LETTER, PLACE> newConfiguration = config.getCopy();
					newConfiguration.addEvents(potentialLassoConfiguration.getConfigEvents());
					newConfiguration.addLoopEvent(event);
					mToBeExaminedConcurrentEndEvents.add(newConfiguration);
				}
			}
		}
		for (final PotentialLassoConfiguration<LETTER, PLACE> configuration : mToBeExaminedConcurrentEndEvents) {
			checkSCCConfig(configuration);
		}
		mConcurrentEndEventPowerset.addAll(mToBeExaminedConcurrentEndEvents);
		mToBeExaminedConcurrentEndEvents.clear();
	}

	private final Set<PotentialLassoConfiguration<LETTER, PLACE>>
			getNeighbourPotentialLassos(final Event<LETTER, PLACE> event) {
		final Set<PotentialLassoConfiguration<LETTER, PLACE>> newPotentialLassos = new HashSet<>();
		final Set<PLACE> succSet = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : event.getSuccessorConditions()) {
			succSet.add(condition.getPlace());
		}
		for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
			for (final Set<Event<LETTER, PLACE>> neighbourConfig : mTransitionToAllLocalConfigsMap
					.get(event2.getTransition())) {
				for (final Event<LETTER, PLACE> event3 : neighbourConfig) {
					final Set<PLACE> preds = new HashSet<>();
					for (final Condition<LETTER, PLACE> condition : event3.getPredecessorConditions()) {
						preds.add(condition.getPlace());
					}
					if (succSet.stream().anyMatch(preds::contains)) {
						newPotentialLassos.add(createPotentialLassoConfig(event, event2, event3, neighbourConfig));
					}
				}
			}
		}
		return newPotentialLassos;
	}

	private final PotentialLassoConfiguration<LETTER, PLACE> createPotentialLassoConfig(
			final Event<LETTER, PLACE> mainEvent, final Event<LETTER, PLACE> originLocalEvent,
			final Event<LETTER, PLACE> neighbourHeadevent, final Set<Event<LETTER, PLACE>> neighbourConfig) {
		final PotentialLassoConfiguration<LETTER, PLACE> newLassoConfiguration =
				new PotentialLassoConfiguration<>(mainEvent);
		final Set<Event<LETTER, PLACE>> allLoopEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> event : mainEvent.getLocalConfiguration()) {
			if (event.getLocalConfiguration().contains(originLocalEvent)) {
				allLoopEvents.add(event);
			}
		}
		for (final Event<LETTER, PLACE> event : neighbourConfig) {
			if (event.getLocalConfiguration().contains(neighbourHeadevent)) {
				allLoopEvents.add(event);
			}
		}
		newLassoConfiguration.addEvents(allLoopEvents);
		return newLassoConfiguration;
	}

	private final boolean checkSCCConfig(final PotentialLassoConfiguration<LETTER, PLACE> configuration)
			throws PetriNetNot1SafeException {

		final ArrayList<PLACE> succs = new ArrayList<>();
		final ArrayList<PLACE> preds = new ArrayList<>();
		final List<Event<LETTER, PLACE>> sccEventList = new ArrayList<>();
		for (final Event<LETTER, PLACE> SCC : configuration.getConfigEvents()) {
			sccEventList.add(SCC);
			preds.addAll(SCC.getTransition().getPredecessors());
			succs.addAll(SCC.getTransition().getSuccessors());
		}
		if (succs.containsAll(preds)) {
			checkIfSCCsFeasible(sccEventList);
		}
		return false;
	}

	private boolean checkIfSCCsFeasible(final List<Event<LETTER, PLACE>> SCC) throws PetriNetNot1SafeException {

		final var allStartConfigs = getallEvents(SCC);
		final List<Transition<LETTER, PLACE>> transitionSCCList = new ArrayList<>();
		for (final Event<LETTER, PLACE> sccEvent : SCC) {
			transitionSCCList.add(sccEvent.getTransition());
		}

		for (final Set<Event<LETTER, PLACE>> startconfigEvent : allStartConfigs) {
			final Set<Transition<LETTER, PLACE>> startconfig = new HashSet<>();
			for (final Event<LETTER, PLACE> startevent : startconfigEvent) {
				startconfig.add(startevent.getTransition());
			}
			final Set<PLACE> startPlaces = new HashSet<>();
			boolean notValidStart = false;
			for (final Transition<LETTER, PLACE> startTransition : startconfig) {
				if (startPlaces.stream().anyMatch(startTransition.getPredecessors()::contains)) {
					notValidStart = true;
					break;
				}
				startPlaces.addAll(startTransition.getPredecessors());
			}
			if (notValidStart) {
				continue;
			}
			final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(startPlaces));
			final Marking<PLACE> realstartMarking = new Marking<>(ImmutableSet.of(startPlaces));
			final Set<FireSequenceInProgress<LETTER, PLACE>> realSet = new HashSet<>();
			final List<Marking<PLACE>> markingList = new ArrayList<>();
			markingList.add(startMarking);
			realSet.add(new FireSequenceInProgress<>(new ArrayList<>(), markingList, new ArrayList<>(), startconfig,
					transitionSCCList, realstartMarking, startconfigEvent));

			while (!realSet.isEmpty()) {
				final Set<FireSequenceInProgress<LETTER, PLACE>> newrealSet = new HashSet<>();

				for (final FireSequenceInProgress<LETTER, PLACE> firesequence : realSet) {
					if (firesequence.getOrderedLoopTransitionList().size() > 0
							&& firesequence.getCurrentMarking().stream().allMatch(realstartMarking::contains)
							&& realstartMarking.stream().allMatch(firesequence.getCurrentMarking()::contains)) {
						final var isLasso = checkForLasso(firesequence);
						if (isLasso) {
							mLogger.info("FOUND SCC:");
							mLogger.info(firesequence.getOrderedLoopTransitionList());
							checkForActualReachability(firesequence);
						}
					}
					for (final Transition<LETTER, PLACE> transition : firesequence.getstillToFireTransitions()) {
						if (firesequence.getCurrentMarking().isTransitionEnabled(transition)) {
							final Set<PLACE> predSet = new HashSet<>(transition.getSuccessors());
							predSet.removeAll(transition.getPredecessors());
							// not possible in a 1-safe net, so discard this line of firing
							if (predSet.stream().anyMatch(firesequence.getCurrentMarking()::contains)) {
								continue;
							}
							final var newFireSequence = firesequence.getCopy();
							newFireSequence.addNewIteration(transition, transition.getSymbol());
							newrealSet.add(newFireSequence);
						}
					}
				}
				realSet.clear();
				realSet.addAll(newrealSet);
			}
		}
		return false;
	}

	private Set<Set<Event<LETTER, PLACE>>> getallEvents(final List<Event<LETTER, PLACE>> sCC) {
		final Set<Set<Event<LETTER, PLACE>>> singletons = new HashSet<>();
		for (final Event<LETTER, PLACE> transition : sCC) {
			final Set<Event<LETTER, PLACE>> newSingletonSet = new HashSet<>();
			newSingletonSet.add(transition);
			singletons.add(newSingletonSet);
		}
		final Set<Set<Event<LETTER, PLACE>>> newSCCSet = new HashSet<>();
		newSCCSet.addAll(singletons);
		for (int i = 0; i < singletons.size(); i++) {
			final Set<Set<Event<LETTER, PLACE>>> newSCCSet2 = new HashSet<>();
			for (final Set<Event<LETTER, PLACE>> set : newSCCSet) {
				for (final Set<Event<LETTER, PLACE>> set2 : singletons) {
					final Set<Event<LETTER, PLACE>> newSCC = new HashSet<>();
					for (final Event<LETTER, PLACE> event : set2) {
						if (!fitsInEqualSet2(event, set)) {
							continue;
						}
					}
					newSCC.addAll(set);
					newSCC.addAll(set2);
					newSCCSet2.add(newSCC);
				}

			}
			newSCCSet.addAll(newSCCSet2);
			newSCCSet2.clear();
		}
		return newSCCSet;
	}

	private final boolean checkForLasso(final FireSequenceInProgress<LETTER, PLACE> firesequence)
			throws PetriNetNot1SafeException {
		Marking<PLACE> currentMarking = firesequence.getCurrentMarking();
		final Marking<PLACE> currentMarkingCopy =
				new Marking<>(ImmutableSet.of(firesequence.getCurrentMarking().stream().collect(Collectors.toSet())));
		for (final Transition<LETTER, PLACE> transition : firesequence.getOrderedLoopTransitionList()) {
			if (!currentMarking.isTransitionEnabled(transition)) {
				return false;
			}
			currentMarking = currentMarking.fireTransition(transition);
		}
		if (!currentMarkingCopy.stream().allMatch(currentMarking::contains)) {
			return false;
		}
		return true;
	}

	private boolean checkForActualReachability(final FireSequenceInProgress<LETTER, PLACE> firesequence)
			throws PetriNetNot1SafeException {
		final Set<Event<LETTER, PLACE>> allEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> event : firesequence.getmStartEvents()) {
			for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
				if (event2 != event) {
					allEvents.add(event2);
				}
			}
		}

		final List<Transition<LETTER, PLACE>> allTransitions = new ArrayList<>();
		for (final Event<LETTER, PLACE> event : allEvents) {
			for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()) {
				for (final Event<LETTER, PLACE> event3 : mTransitionToAllPredecessorsMap.get(event2.getTransition())) {
					allTransitions.add(event3.getTransition());
				}
				allTransitions.add(event.getTransition());
			}
		}
		// TODO CHANGE STEM SEARCH TO USE THE METHOD BELOW (WHICH IS NOT USED RIGHT NOW AND IS DEAD CODE) --
		final Set<PLACE> predSet = new HashSet<>();
		for (final Event<LETTER, PLACE> event2 : firesequence.getmStartEvents()) {
			for (final Condition<LETTER, PLACE> condition : event2.getPredecessorConditions()) {
				predSet.add(condition.getPlace());
			}
		}
		for (final Pair<Set<Event<LETTER, PLACE>>, Set<PLACE>> pair : mConcurrentlyReachablePlaceSetsPairs) {
			if (pair.getSecond().containsAll(predSet)) {
				// mLogger.info("FOUND ENABLER");
			}
		}
		// --

		final var orderedStem = getFittingStem(firesequence, allTransitions);
		for (final Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>> pair : orderedStem) {
			if (pair == null) {
				continue;
			}
			getLasso2(pair, firesequence);
		}
		return false;
	}

	private Set<Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>>> getFittingStem(
			final FireSequenceInProgress<LETTER, PLACE> firesequence,
			final List<Transition<LETTER, PLACE>> allTransitions) throws PetriNetNot1SafeException {
		final Set<Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>>> allStemSet = new HashSet<>();
		final List<PLACE> neededPlaces = new ArrayList<>();
		for (final Event<LETTER, PLACE> event : firesequence.getmStartEvents()) {
			neededPlaces.addAll(event.getTransition().getPredecessors());
		}
		// final List<Transition<LETTER, PLACE>> allTransitions = new ArrayList<>();
		// for (final Event<LETTER, PLACE> event : allEvents) {
		// allTransitions.add(event.getTransition());
		// }
		final Set<Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>>> buildingStemSet = new HashSet<>();
		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()));

		if (allTransitions.size() == 0) {
			allStemSet.add(new Pair<>(new ArrayList<>(), startMarking));
			return allStemSet;
		}

		for (final Transition<LETTER, PLACE> transition : allTransitions) {
			if (startMarking.isTransitionEnabled(transition)) {
				final List<Transition<LETTER, PLACE>> singletonList = new ArrayList<>();
				singletonList.add(transition);
				final Marking<PLACE> newMarking =
						new Marking<>(ImmutableSet.of(startMarking.stream().collect(Collectors.toSet())));
				buildingStemSet.add(new Pair<>(singletonList, newMarking.fireTransition(transition)));
			}
		}

		for (int i = 0; i < allTransitions.size(); i++) {
			for (final Transition<LETTER, PLACE> transition : allTransitions) {
				final Set<Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>>> newbuildingStemSet = new HashSet<>();
				final Set<Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>>> stemsToRemove = new HashSet<>();
				for (final Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>> stem : buildingStemSet) {
					final List<PLACE> markingPlaces = new ArrayList<>();
					for (final PLACE place : stem.getSecond()) {
						markingPlaces.add(place);
					}
					if (markingPlaces.containsAll(neededPlaces)) {
						// mLogger.info("Found stem for SCC");
						allStemSet.add(stem);
					}
					if ((!stem.getFirst().contains(transition)) && stem.getSecond().isTransitionEnabled(transition)) {
						final List<Transition<LETTER, PLACE>> newStemList = new ArrayList<>(stem.getFirst());
						newStemList.add(transition);
						final Marking<PLACE> newMarking =
								new Marking<>(ImmutableSet.of(stem.getSecond().stream().collect(Collectors.toSet())));
						newbuildingStemSet.add(new Pair<>(newStemList, newMarking.fireTransition(transition)));
						stemsToRemove.add(stem);
					}
				}
				buildingStemSet.removeAll(stemsToRemove);
				buildingStemSet.addAll(newbuildingStemSet);
			}
		}
		return allStemSet;
	}

	private void getLasso2(final Pair<List<Transition<LETTER, PLACE>>, Marking<PLACE>> orderedStem,
			final FireSequenceInProgress<LETTER, PLACE> fireSequenceInProgress) throws PetriNetNot1SafeException {
		Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()));
		final List<LETTER> stemLetters = new ArrayList<>();
		final List<LETTER> loopLetters = new ArrayList<>();
		final List<Marking<PLACE>> sequenceOfStemMarkings = new ArrayList<>();
		final List<Marking<PLACE>> sequenceOfLassoMarkings = new ArrayList<>();
		sequenceOfStemMarkings.add(startMarking);
		for (final Transition<LETTER, PLACE> transition : orderedStem.getFirst()) {
			stemLetters.add(transition.getSymbol());
			startMarking = startMarking.fireTransition(transition);
			sequenceOfStemMarkings.add(startMarking);
		}
		sequenceOfLassoMarkings.add(startMarking);
		for (final Transition<LETTER, PLACE> transition : fireSequenceInProgress.getOrderedLoopTransitionList()) {
			loopLetters.add(transition.getSymbol());
			startMarking = startMarking.fireTransition(transition);
			sequenceOfLassoMarkings.add(startMarking);
		}

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
		final boolean accpted = isAccepted(nestedLassoWord);

		if (accpted) {
			mRun = lassoRun;
		}
	}

	abstract boolean isAccepted(NestedLassoWord<LETTER> nestedLassoWord) throws PetriNetNot1SafeException;

	private final boolean fitsInEqualSet(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config) {
		for (final Event<LETTER, PLACE> event2 : config.getLoopEvents()) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	private final boolean fitsInEqualSet2(final Event<LETTER, PLACE> event, final Set<Event<LETTER, PLACE>> set) {
		for (final Event<LETTER, PLACE> event2 : set) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	abstract boolean meetsConditionsToBeBaseOfLassoConfiguration(Event<LETTER, PLACE> event);

	abstract boolean extendsConfiguration(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config);
}
