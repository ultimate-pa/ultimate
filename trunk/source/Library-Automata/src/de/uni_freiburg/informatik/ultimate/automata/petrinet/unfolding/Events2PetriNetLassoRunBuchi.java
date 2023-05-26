package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Given stem and loop events of supposed accepting lasso word, if valid, {@link PetriNetLassoRun} is built.
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class Events2PetriNetLassoRunBuchi<LETTER, PLACE> {
	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	private final List<Event<LETTER, PLACE>> mConfigStemPart;
	private final List<Event<LETTER, PLACE>> mConfigLoopPart;

	public Events2PetriNetLassoRunBuchi(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart, final BranchingProcess<LETTER, PLACE> unfolding) {
		mUnfolding = unfolding;
		mConfigStemPart = configStemPart;
		mConfigLoopPart = configLoopPart;
	}

	public boolean isAccepted() {
		return mConfigLoopPart.stream().flatMap(x -> x.getTransition().getSuccessors().stream())
				.anyMatch(mUnfolding.getNet()::isAccepting);
	}

	/**
	 * Given loop and stem events, checks if the respective Transitions actually build a valid lasso-run in the
	 * Petri-Net.
	 */
	public PetriNetLassoRun<LETTER, PLACE> constructLassoRun() throws PetriNetNot1SafeException {
		final List<Transition<LETTER, PLACE>> stemTransitions =
				mConfigStemPart.stream().map(Event::getTransition).collect(Collectors.toList());
		final List<Transition<LETTER, PLACE>> loopTransitions =
				mConfigLoopPart.stream().map(Event::getTransition).collect(Collectors.toList());

		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mUnfolding.getNet().getInitialPlaces()));

		final PetriNetRun<LETTER, PLACE> stemRun = constructRun(startMarking, stemTransitions);
		final PetriNetRun<LETTER, PLACE> loopRun =
				constructRun(stemRun.getMarking(stemRun.getLength() - 1), loopTransitions);

		return new PetriNetLassoRun<>(stemRun, loopRun);
	}

	/**
	 * Given a sorted List of transitions which build a valid firesequence, builds a valid {@PetriNetRun}.
	 *
	 * @param initialMarking
	 *            of the Petri-Net
	 * @param transitions,
	 *            the "sorted" Transitions which build the lasso-word
	 * @return A valid PetriNetRun
	 * @throws PetriNetNot1SafeException
	 */
	@SuppressWarnings("unchecked")
	private final PetriNetRun<LETTER, PLACE> constructRun(final Marking<PLACE> initialMarking,
			final List<Transition<LETTER, PLACE>> transitions) throws PetriNetNot1SafeException {
		final List<LETTER> word = new ArrayList<>();
		final List<Marking<PLACE>> markings = new ArrayList<>();
		final List<Transition<LETTER, PLACE>> resultTransitions = new ArrayList<>();
		markings.add(initialMarking);
		Marking<PLACE> currentMarking = initialMarking;
		for (final Transition<LETTER, PLACE> transition : transitions) {
			word.add(transition.getSymbol());
			currentMarking = currentMarking.fireTransition(transition);
			markings.add(currentMarking);
			resultTransitions.add(transition);
		}
		return new PetriNetRun<>(markings, new Word<>((LETTER[]) word.toArray()), resultTransitions);
	}
}
