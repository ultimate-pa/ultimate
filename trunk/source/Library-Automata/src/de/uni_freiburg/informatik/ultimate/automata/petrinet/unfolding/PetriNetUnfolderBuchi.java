package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class PetriNetUnfolderBuchi<LETTER, PLACE> extends PetriNetUnfolderBase<LETTER, PLACE> {
	PetriNetLassoRun<LETTER, PLACE> mLassoRun;

	public PetriNetUnfolderBuchi(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	public PetriNetLassoRun<LETTER, PLACE> getAcceptingRun() {
		return mLassoRun;
	}

	@Override
	protected void createInitialRun() throws PetriNetNot1SafeException {
		return;
	}

	@Override
	protected boolean checkInitialPlaces() {
		return false;
	}

	@Override
	boolean unfoldingSearchSuccessful(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {

		mUnfolding.addEvent(event);

		if (event.isCutoffEvent() && event.getLocalConfiguration().contains(event.getCompanion())) {

			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mUnfolding.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return true;
			}
		}
		return false;
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mUnfolding.getNet().getInitialPlaces()));
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
				(IPetriNetTransitionProvider<LETTER, PLACE>) mUnfolding.getNet(), nestedLassoWord);
		final boolean accpted = accepts.getResult();
		if (accpted) {
			mLassoRun = lassoRun;
			return true;
		}
		return false;
	}

	@Override
	void createOrUpdateRunIfWanted(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		return;
	}

	@Override
	boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		return true;
	}

}
