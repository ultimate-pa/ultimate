package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations.MarkingOfFireSequence;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that provides the Rabin acceptance check for (Rabin-)Petri nets.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
// TODO prefix nur buchi bei allen, alle in petri net operatins
public final class RabinAccepts<LETTER, PLACE> extends AcceptsInfiniteWords<LETTER, PLACE> {

	/**
	 * Constructor. Check if given Rabin-Petri Net accepts given word.
	 *
	 * @param <services>
	 *            Ultimare services.
	 *
	 * @param <operand>
	 *            Input Petri Net.
	 *
	 * @param <word>
	 *            Input word.
	 */
	public RabinAccepts(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final NestedLassoWord<LETTER> word) throws PetriNetNot1SafeException {
		super(services, operand, word);
	}

	/**
	 * Creates a {@link MarkingOfFireSequence} with information if an accepted or finite place was fired into.
	 */
	@Override
	MarkingOfFireSequence<LETTER, PLACE> getSuccessorMarkingOfFireSequence(
			final MarkingOfFireSequence<LETTER, PLACE> predecessor, final Transition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException {
		int firingInAcceptingPlaceIndex;
		if (transition.getSuccessors().stream().anyMatch(mOperand::isAccepting)) {
			firingInAcceptingPlaceIndex = mFireSequenceIndex;
		} else {
			firingInAcceptingPlaceIndex = predecessor.getLastIndexOfShootingAcceptingStateInFireSequence();
		}
		int firingInLimitedPlaceIndex;
		if (transition.getSuccessors().stream()
				.anyMatch(((IRabinPetriNet<LETTER, PLACE>) mOperand).getFinitePlaces()::contains)) {
			firingInLimitedPlaceIndex = mFireSequenceIndex;
		} else {
			firingInLimitedPlaceIndex = predecessor.getLastIndexOfShootingFinitePlaceInFireSequence();
		}
		return new MarkingOfFireSequence<>(predecessor.getMarking().fireTransition(transition),
				predecessor.getHondaMarkingsOfFireSequence(), mFireSequenceIndex, firingInAcceptingPlaceIndex,
				firingInLimitedPlaceIndex);
	}

	@Override
	boolean checkForAcceptingConditions() {
		for (final Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer> markingAndHondaIndex : containsLoopingFiresequence(
				mFireSequenceTreeMarkings)) {
			if ((markingAndHondaIndex.getFirst()
					.getLastIndexOfShootingAcceptingStateInFireSequence() >= markingAndHondaIndex.getSecond())
					&& (markingAndHondaIndex.getFirst()
							.getLastIndexOfShootingFinitePlaceInFireSequence() < markingAndHondaIndex.getSecond())) {
				return true;
			}
			// any nonaccepting firing sequence stuck in a loop is disregarded
			mFireSequenceTreeMarkings.remove(markingAndHondaIndex.getFirst());
		}
		return false;
	}
}
