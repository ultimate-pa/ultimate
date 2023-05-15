package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Given stem and loop events of supposed accepting lasso word, if valid, {@link PetriNetLassoRun} is built.
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class Events2PetriNetLassoRunBuchi<LETTER, PLACE> {
	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	private final AutomataLibraryServices mServices;
	private final PetriNetLassoRun<LETTER, PLACE> mLassoRun;

	public Events2PetriNetLassoRunBuchi(final AutomataLibraryServices services,
			final List<Event<LETTER, PLACE>> configLoopPart, final List<Event<LETTER, PLACE>> configStemPart,
			final BranchingProcess<LETTER, PLACE> unfolding) throws PetriNetNot1SafeException {
		mServices = services;
		mUnfolding = unfolding;
		mLassoRun = checkIfLassoConfigurationAccepted(configLoopPart, configStemPart);
	}

	public final PetriNetLassoRun<LETTER, PLACE> getLassoRun() {
		return mLassoRun;
	}

	/**
	 * Given loop and stem events we build a {@link PetriNetLassoRun}.
	 *
	 * @param configLoopPart
	 * @param configStemPart
	 * @return
	 * @throws PetriNetNot1SafeException
	 */
	private final PetriNetLassoRun<LETTER, PLACE> checkIfLassoConfigurationAccepted(
			final List<Event<LETTER, PLACE>> configLoopPart, final List<Event<LETTER, PLACE>> configStemPart)
			throws PetriNetNot1SafeException {
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
			return null;
		}

		for (final Event<LETTER, PLACE> stemEvent : configStemPart) {
			stemTransitions.add(stemEvent.getTransition());
		}

		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mUnfolding.getNet().getInitialPlaces()));

		final PetriNetRun<LETTER, PLACE> stemRun = constructRun(startMarking, stemTransitions);
		final PetriNetRun<LETTER, PLACE> loopRun =
				constructRun(stemRun.getMarking(stemRun.getLength() - 1), loopTransitions);

		return createAndCheckLassoRun(stemRun, loopRun);
	}

	@SuppressWarnings("unchecked")
	private final PetriNetRun<LETTER, PLACE> constructRun(final Marking<PLACE> initialMarking,
			final List<Transition<LETTER, PLACE>> transitions) throws PetriNetNot1SafeException {
		// TODO: Check this method for theroetical correctness
		// Since some number of events might be in concurrency the sorting might have not returned the correct
		// order of events. We thus juggle non enabled events in this stack always trying if they are enabled
		// in the next iteration.
		final List<LETTER> word = new ArrayList<>();
		final List<Marking<PLACE>> markings = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> resultTransitions = new ArrayList<>();
		final Deque<Transition<LETTER, PLACE>> waitingLoopTransitionStack = new ArrayDeque<>();
		markings.add(initialMarking);
		Marking<PLACE> currentMarking = initialMarking;
		for (final Transition<LETTER, PLACE> transition : transitions) {
			for (int i = 0; i < waitingLoopTransitionStack.size(); i++) {
				final var waitingTransition = waitingLoopTransitionStack.pop();
				if (currentMarking.isTransitionEnabled(waitingTransition)) {
					word.add(waitingTransition.getSymbol());
					currentMarking = currentMarking.fireTransition(waitingTransition);
					markings.add(currentMarking);
					resultTransitions.add(waitingTransition);
				} else {
					waitingLoopTransitionStack.addFirst(transition);
				}
			}

			if (!currentMarking.isTransitionEnabled(transition)) {
				waitingLoopTransitionStack.push(transition);
				continue;
			}
			word.add(transition.getSymbol());
			currentMarking = currentMarking.fireTransition(transition);
			markings.add(currentMarking);
			resultTransitions.add(transition);
		}
		return new PetriNetRun<>(markings, new Word<>((LETTER[]) word.toArray()), resultTransitions);
	}

	private final PetriNetLassoRun<LETTER, PLACE> createAndCheckLassoRun(final PetriNetRun<LETTER, PLACE> stemRun,
			final PetriNetRun<LETTER, PLACE> loopRun) throws PetriNetNot1SafeException {
		final NestedLassoWord<LETTER> nestedLassoWord = new NestedLassoWord<>(NestedWord.nestedWord(stemRun.getWord()),
				NestedWord.nestedWord(loopRun.getWord()));
		final PetriNetLassoRun<LETTER, PLACE> lassoRun = new PetriNetLassoRun<>(stemRun, loopRun);
		// TODO: this BuchiAccepts should not be needed, but acts as a last correctness check for unknown edge cases
		final BuchiAccepts<LETTER, PLACE> accepts = new BuchiAccepts<>(mServices,
				(IPetriNetTransitionProvider<LETTER, PLACE>) mUnfolding.getNet(), nestedLassoWord);
		if (accepts.getResult()) {
			return lassoRun;
		}
		return null;
	}
}
