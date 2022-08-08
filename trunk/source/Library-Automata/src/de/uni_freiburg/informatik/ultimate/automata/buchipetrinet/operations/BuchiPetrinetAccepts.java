package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Class that provides the Buchi acceptance check for (Buchi-)Petri nets.
 * 
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public final class BuchiPetrinetAccepts<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	/*
	 * The Petri net which we check acceptance for.
	 */
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mOperand;
	private final Marking<LETTER, PLACE> mInitialMarking;
	/*
	 * The word we check acceptance for.
	 */
	private final NestedLassoWord<LETTER> mLassoWord;
	/*
	 * Through nondeterminism in the Petri net one input word can produce multiple different fire sequences. Thus we
	 * could think of the multiple firesequences as a combined fire sequence tree where we have splits when
	 * nondeterministic transitions occur.<p> During the traversal of the input word in isWordAcceptedByBuchiPetriNet()
	 * mFireSequenceTreeMarkings contains all markings of the different firing sequences at the current index of the
	 * word.
	 */
	private Set<MarkingOfFireSequence<LETTER, PLACE>> mFireSequenceTreeMarkings;
	private boolean misInLoopPart;
	private final boolean mResult;

	/*
	 * Constructor. Check if given Buchi-Petri Net accepts given word.
	 * 
	 * @param <services> Ultimare services.
	 * 
	 * @param <operand> Input Petri Net.
	 * 
	 * @param <word> Input word.
	 */
	public BuchiPetrinetAccepts(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final NestedLassoWord<LETTER> word)
			throws PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mInitialMarking = new Marking<>(ImmutableSet.of(operand.getInitialPlaces()));
		mLassoWord = word;
		misInLoopPart = false;
		mFireSequenceTreeMarkings = new HashSet<>();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = isWordAcceptedByBuchiPetriNet();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public Object getResult() {
		return mResult;
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	/*
	 * Calculates all fire sequences of input word on the Buchi-Petrinet (multiple because of possible nondeterminism of
	 * the net) and checks if one of those fire sequences is accepting.
	 * 
	 * @return boolean representing if word is accepted by net.
	 */
	private final boolean isWordAcceptedByBuchiPetriNet() throws PetriNetNot1SafeException {
		computeHondaMarkingsFromInitialMarking();
		misInLoopPart = true;
		return computeLoopMarkingsAndCheckForAcceptance();
	}

	private void computeHondaMarkingsFromInitialMarking() throws PetriNetNot1SafeException {
		mFireSequenceTreeMarkings.add(new MarkingOfFireSequence<>(mInitialMarking, mInitialMarking, false));
		for (LETTER symbol : mLassoWord.getStem()) {
			produceSuccessorMarkingsOfFireSequenceOfSet(symbol);
		}
		// at this point of the fire sequence tree the markings are the hondamarkings
		for (MarkingOfFireSequence<LETTER, PLACE> marking : mFireSequenceTreeMarkings) {
			marking.setHondaMarkingOfFireSequence(marking.getMarking());
		}
	}

	private final boolean computeLoopMarkingsAndCheckForAcceptance() throws PetriNetNot1SafeException {
		for (LETTER symbol : mLassoWord.getLoop()) {
			produceSuccessorMarkingsOfFireSequenceOfSet(symbol);
		}
		return containsAcceptingFiresequence(mFireSequenceTreeMarkings);
	}

	private void produceSuccessorMarkingsOfFireSequenceOfSet(final LETTER currentSymbol)
			throws PetriNetNot1SafeException {
		final Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingSet = new HashSet<>();
		for (MarkingOfFireSequence<LETTER, PLACE> markingOfFireSequence : mFireSequenceTreeMarkings) {
			successorMarkingSet.addAll(getSuccessorMarkingsOfFireSequence(markingOfFireSequence, currentSymbol));
		}
		mFireSequenceTreeMarkings = successorMarkingSet;
	}

	private Set<MarkingOfFireSequence<LETTER, PLACE>> getSuccessorMarkingsOfFireSequence(
			MarkingOfFireSequence<LETTER, PLACE> predeccessorMarking, final LETTER currentSymbol)
			throws PetriNetNot1SafeException {

		final Set<ITransition<LETTER, PLACE>> enabledTransitionSet =
				activeTransitionsWithSymbol(predeccessorMarking.getMarking(), currentSymbol);

		final Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingsOfFireSequence = new HashSet<>();
		for (final ITransition<LETTER, PLACE> transition : enabledTransitionSet) {
			successorMarkingsOfFireSequence.add(getSuccessorMarkingOfFireSequence(predeccessorMarking, transition));
		}
		return successorMarkingsOfFireSequence;
	}

	private MarkingOfFireSequence<LETTER, PLACE> getSuccessorMarkingOfFireSequence(
			MarkingOfFireSequence<LETTER, PLACE> predecessor, ITransition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException {
		boolean firedIntoAcceptingStateBoolean = misInLoopPart && (predecessor.getAcceptingPlaceSeenInLoopBoolean()
				|| mOperand.getSuccessors(transition).stream().anyMatch(mOperand::isAccepting));
		return new MarkingOfFireSequence<>(predecessor.getMarking().fireTransition(transition, mOperand),
				predecessor.getHondaMarkingOfFireSequence(), firedIntoAcceptingStateBoolean);
	}

	private Set<ITransition<LETTER, PLACE>> activeTransitionsWithSymbol(final Marking<LETTER, PLACE> marking,
			final LETTER symbol) {
		final Set<ITransition<LETTER, PLACE>> activeTransitionsWithSymbol = new HashSet<>();
		for (final PLACE place : marking) {
			mOperand.getSuccessors(place).stream().filter(transition -> transition.getSymbol().equals(symbol))
					.filter((transition -> marking.isTransitionEnabled(transition, mOperand)))
					.collect(Collectors.toSet()).forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}

	/*
	 * This method computes if in the given set of markings, there is a marking which is atleast as strong as the honda
	 * marking m' of its fire sequence. <p> A marking m being as strong as a marking m' means for any place p where
	 * m'(p) = n, m(p) >= n has to hold. The reason we do this is if at the end of the supposed loop of a lasso if the
	 * resulting marking is as strong as the honda marking, we know that we have an actual feasible loop in the Petri
	 * net.
	 * 
	 * @param <markingSet> The set of markings we want to test.
	 * 
	 * @param <comparedMarking> The marking we want to find an as strong marking for.
	 * 
	 * @return boolean representing if a marking of the set is as strong as the comparedMarking.
	 */
	private final boolean containsAcceptingFiresequence(final Set<MarkingOfFireSequence<LETTER, PLACE>> markingSet) {
		for (MarkingOfFireSequence<LETTER, PLACE> marking : markingSet) {
			final Set<PLACE> comparedMarkingPlaceSet =
					marking.getHondaMarkingOfFireSequence().stream().collect(Collectors.toSet());
			if (marking.getMarking().containsAll(comparedMarkingPlaceSet)
					&& marking.getAcceptingPlaceSeenInLoopBoolean()) {
				return true;
			}
		}
		return false;
	}
}
