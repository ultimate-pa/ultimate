package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that provides the Buchi acceptance check for (Buchi-)Petri nets.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
// TODO prefix nur buchi bei allen, alle in petri net operatins
public final class BuchiAccepts<LETTER, PLACE> extends AcceptsInfiniteWords<LETTER, PLACE> {

	/**
	 * Constructor. Check if given Buchi-Petri Net accepts given word.
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
	public BuchiAccepts(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final NestedLassoWord<LETTER> word)
			throws PetriNetNot1SafeException {
		super(services, operand, word);
	}

	@Override
	MarkingOfFireSequence<LETTER, PLACE> getSuccessorMarkingOfFireSequence(
			final MarkingOfFireSequence<LETTER, PLACE> predecessor, final Transition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException {
		int firingInAcceptingPlaceIndex;
		if (transition.getSuccessors().stream().anyMatch(mOperand::isAccepting)) {
			firingInAcceptingPlaceIndex = mfireSequenceIndex;
		} else {
			firingInAcceptingPlaceIndex = predecessor.getLastIndexOfShootingAcceptingStateInFireSequence();
		}
		return new MarkingOfFireSequence<>(predecessor.getMarking().fireTransition(transition),
				predecessor.getHondaMarkingsOfFireSequence(), mfireSequenceIndex, firingInAcceptingPlaceIndex, 0);
	}

	@Override
	boolean checkForAcceptingConditions() {
		for (final Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer> markingAndHondaIndex : containsLoopingFiresequence(
				mFireSequenceTreeMarkings)) {
			if (markingAndHondaIndex.getFirst()
					.getLastIndexOfShootingAcceptingStateInFireSequence() >= markingAndHondaIndex.getSecond()) {
				return true;
			}
			// any nonaccepting firing sequence stuck in a loop is disregarded
			mFireSequenceTreeMarkings.remove(markingAndHondaIndex.getFirst());
		}
		return false;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of accepts");
		}
		final boolean resultAutomata =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts<>(mServices,
						(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
								(IBlackWhiteStateFactory<PLACE>) stateFactory, mOperand)).getResult(),
						mLassoWord)).getResult();
		final boolean correct = mResult == resultAutomata;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of accepts");
		}

		return correct;
	}

	public boolean checkResultReal(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory,
			final IBlackWhiteStateFactory<PLACE> blackWhite) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of accepts");
		}
		final boolean resultAutomata =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts<>(mServices,
						(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory, blackWhite, mOperand))
								.getResult(),
						mLassoWord)).getResult();
		final boolean correct = mResult == resultAutomata;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of accepts");
		}

		return correct;
	}

}
