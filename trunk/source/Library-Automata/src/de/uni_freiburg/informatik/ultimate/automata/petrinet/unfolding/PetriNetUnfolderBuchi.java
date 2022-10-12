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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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

	/**
	 * Checks words contained in local configuration for being accepted lasso words.
	 *
	 * @param configLoopPart
	 * @param configStemPart
	 * @return if lassoword was found
	 * @throws PetriNetNot1SafeException
	 */
	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		mLogger.info("Type 2 Lasso search started.");
		final List<Transition<LETTER, PLACE>> stemTransitions = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> loopTransitions = new ArrayList<>();

		boolean acceptingPlaceShotintoInLoop = false;
		for (final Event<LETTER, PLACE> loopEvent : configLoopPart) {
			if (loopEvent.getTransition().getSuccessors().stream().anyMatch(mUnfolding.getNet()::isAccepting)) {
				acceptingPlaceShotintoInLoop = true;
			}
			loopTransitions.add(loopEvent.getTransition());
		}
		if (!acceptingPlaceShotintoInLoop) {
			mLogger.info("Type 2 Lasso search ended.");
			return false;
		}

		for (final Event<LETTER, PLACE> stemEvent : configStemPart) {
			stemTransitions.add(stemEvent.getTransition());
		}

		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mUnfolding.getNet().getInitialPlaces()));

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

		mLogger.info("Type 2 Lasso search ended.");
		return createAndCheckLassoRun(stemLetters, sequenceOfStemMarkings, loopLetters, sequenceOfLassoMarkings);
	}

	private final Pair<List<LETTER>, List<Marking<PLACE>>> constructFeasibleLetterAndMarkingSequence(
			Marking<PLACE> startMarking, final List<Transition<LETTER, PLACE>> loopTransitions)
			throws PetriNetNot1SafeException {
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
