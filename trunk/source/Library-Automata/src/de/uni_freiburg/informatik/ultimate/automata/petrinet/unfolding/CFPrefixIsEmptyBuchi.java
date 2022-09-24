package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
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

/**
 * Checks if complete finite prefix contains accepting lasso configuration.
 *
 */
public class CFPrefixIsEmptyBuchi<LETTER, PLACE> {
	BranchingProcess<LETTER, PLACE> mCompletePrefix;
	Set<Event<LETTER, PLACE>> mCutoffEvents = new HashSet<>();
	Set<Event<LETTER, PLACE>> mLoopCutoffEvents = new HashSet<>();
	Set<Event<LETTER, PLACE>> mOriginLoopCutoffEvents = new HashSet<>();
	public PetriNetLassoRun<LETTER, PLACE> mRun = null;
	AutomataLibraryServices mServices;
	protected final ILogger mLogger;

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

	private boolean getResult() {
		return mRun == null;
	}

	private void search() {
		mLogger.info("Starting cutoff event analysis.");
		for (final Event<LETTER, PLACE> event : mCompletePrefix.getCutoffEvents()) {
			// TODO: actually slows us down, any other way to check ?
			// final var config = event.getLocalConfiguration();
			// boolean potentialLasso = false;
			// for (final Event<LETTER, PLACE> configEvent : config) {
			// if (configEvent.getSuccessorConditions().stream()
			// .anyMatch(mCompletePrefix.getAcceptingConditions()::contains)) {
			// potentialLasso = true;
			// break;
			// }
			// }
			// if (!potentialLasso) {
			// continue;
			// }
			if (event.getLocalConfiguration().contains(event.getCompanion())) {
				mLoopCutoffEvents.add(event);
			} else if (event.getCompanion().getTransition() == null) {
				mOriginLoopCutoffEvents.add(event);
			} else {
				mCutoffEvents.add(event);
			}
		}
		mLogger.info("Ended cutoff event analysis.");
	}

	private void investigateCutOffs() throws PetriNetNot1SafeException {
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
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return;
			}
		}
		mLogger.info("Type 2 Lasso search ended.");
		mLogger.info("Type 3 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mCutoffEvents) {
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()) {
				if (configEvent.isCompanion()) {
					for (final Event<LETTER, PLACE> event2 : configEvent.getCutoffEventsThisIsCompanionTo()) {
						if (event2.getLocalConfiguration().contains(event.getCompanion())) {
							final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
							final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
							configLoopEvents.add(event2);
							for (final Event<LETTER, PLACE> configEvent2 : event.getLocalConfiguration()
									.getSortedConfiguration(mCompletePrefix.getOrder())) {
								if (configEvent2 != configEvent
										&& configEvent2.getLocalConfiguration().contains(configEvent)) {
									configLoopEvents.add(configEvent2);
								}
							}
							for (final Event<LETTER, PLACE> companionConfigEvent : event2.getLocalConfiguration()
									.getSortedConfiguration(mCompletePrefix.getOrder())) {
								if (companionConfigEvent != event2) {
									configStemEvents.add(companionConfigEvent);
								}
							}
							if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
								return;
							}
						}
					}
				}
			}
		}
		mLogger.info("Type 3 Lasso search ended.");
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mCompletePrefix.getNet().getInitialPlaces()));
		final List<LETTER> stemLetters = new ArrayList<>();
		final List<LETTER> loopLetters = new ArrayList<>();
		final List<Marking<PLACE>> sequenceOfStemMarkings = new ArrayList<>();
		final List<Marking<PLACE>> sequenceOfLassoMarkings = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> stemTransitions = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> loopTransitions = new ArrayList<>();

		for (final Event<LETTER, PLACE> loopEvent : configLoopPart) {
			loopTransitions.add(loopEvent.getTransition());
		}

		for (final Event<LETTER, PLACE> stemEvent : configStemPart) {
			stemTransitions.add(stemEvent.getTransition());
		}

		// TODO: Check this method for theroetical correctness
		// Since some number of events might be in concurrency the sorting might have not returned the correct
		// order of events. We thus juggle non enabled events in this stack always trying if they are enabled
		// in the next iteration.
		final Deque<Transition<LETTER, PLACE>> waitingStemTransitionStack = new ArrayDeque<>();
		sequenceOfStemMarkings.add(startMarking);
		for (final Transition<LETTER, PLACE> transition : stemTransitions) {
			for (int i = 0; i < waitingStemTransitionStack.size(); i++) {
				final var waitingTransition = waitingStemTransitionStack.pop();
				if (startMarking.isTransitionEnabled(waitingTransition)) {
					stemLetters.add(waitingTransition.getSymbol());
					startMarking = startMarking.fireTransition(waitingTransition);
					sequenceOfStemMarkings.add(startMarking);
				} else {
					waitingStemTransitionStack.addFirst(transition);
				}
			}

			if (!startMarking.isTransitionEnabled(transition)) {
				return false;
			}
			stemLetters.add(transition.getSymbol());
			startMarking = startMarking.fireTransition(transition);
			sequenceOfStemMarkings.add(startMarking);
		}

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
