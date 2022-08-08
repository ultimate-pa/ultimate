package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
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
	private final IPetriNet<LETTER, PLACE> mOperand;
	private final Marking<LETTER, PLACE> mInitialMarking;
	/*
	 * The word we check acceptance for.
	 */
	private final NestedLassoWord<LETTER> mLassoWord;
	/*
	 * Stem and Loop of NestedLassoWord combined as a NestedWord. Used for fire sequence symbol index tracking.
	 */
	private final NestedWord<LETTER> mStemAndLoopWord;
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
	public BuchiPetrinetAccepts(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand,
			final NestedLassoWord<LETTER> word) throws PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mInitialMarking = new Marking<>(ImmutableSet.of(operand.getInitialPlaces()));
		mLassoWord = word;
		mStemAndLoopWord = mLassoWord.getStem().concatenate(mLassoWord.getLoop());

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
	 * Computes if mLassoword is accepted by mOperand (Petri net). Given the word, we do so with a Depth First Search of
	 * possible fire sequences using a stack of markings. For the stack we use {@link MarkingOfFireSequence} to keep
	 * track of the fire sequence index each marking is at and if in the loop of that (lasso-) fire sequence we fired a
	 * token into an accepting state. (which is needed for the Buchi-Petri acceptance condition.)
	 * 
	 * @return a boolean representing if word got accepted or not.
	 */
	private final Boolean isWordAcceptedByBuchiPetriNet() throws PetriNetNot1SafeException {

		final Deque<MarkingOfFireSequence<LETTER, PLACE>> markingsOfFireSequencesStack = new ArrayDeque<>();
		markingsOfFireSequencesStack.push(createInitialMarkingOfFireSequence());
		// Hondamarking denotes the first marking of the lasso part of the firing sequence
		// With this we keep track of what is the hondamarking for the current fire sequence in the DFS.
		Marking<LETTER, PLACE> hondaMarking = new Marking<>(ImmutableSet.of(new HashSet<>()));

		while (!(markingsOfFireSequencesStack.isEmpty())) {
			MarkingOfFireSequence<LETTER, PLACE> poppedMarkingOfFireSequence = markingsOfFireSequencesStack.pop();
			int poppedWordPosition = poppedMarkingOfFireSequence.getRunPosition();
			Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingsOfFireSequence =
					calcSuccessorMarkings(poppedMarkingOfFireSequence);

			if (poppedWordPosition == mLassoWord.getStem().length()) {
				hondaMarking = poppedMarkingOfFireSequence.getMarking();
			}

			if (poppedWordPosition == mStemAndLoopWord.length() - 1) {
				boolean lassoFound = containsStrongerAcceptingMarking(successorMarkingsOfFireSequence, hondaMarking);
				if (lassoFound) {
					return true;
				}
			} else {
				for (MarkingOfFireSequence<LETTER, PLACE> marking : successorMarkingsOfFireSequence) {
					markingsOfFireSequencesStack.push(marking);
				}
			}
		}
		return false;
	}

	private MarkingOfFireSequence<LETTER, PLACE> createInitialMarkingOfFireSequence() {
		final Set<PLACE> firstMarkingPlaceSet = mInitialMarking.stream().collect(Collectors.toSet());
		final Marking<LETTER, PLACE> initialMarkingCopy = new Marking<>(ImmutableSet.of(firstMarkingPlaceSet));
		final int initialWordPosition = 0;
		final boolean acceptingPlaceSeenInLoop = false;
		return (new MarkingOfFireSequence<>(initialMarkingCopy, initialWordPosition, acceptingPlaceSeenInLoop));
	}

	/*
	 * Computes all successor-markings of a given marking with fire sequence index. This method also checks if the fired
	 * transition fires a token inside an accepting place of the Petri net and marks that information with the help of
	 * {@link MarkingOfFireSequence}.
	 * 
	 * @param <predeccessorMarking> Marking (and symbol of transition) as {@link MarkingOfFireSequence} which we want to
	 * know the successors of.
	 * 
	 * @return the set of successor markings as {@link MarkingOfFireSequence} objects.
	 */
	private Set<MarkingOfFireSequence<LETTER, PLACE>> calcSuccessorMarkings(
			MarkingOfFireSequence<LETTER, PLACE> predeccessorMarking) throws PetriNetNot1SafeException {
		final Marking<LETTER, PLACE> poppedMarking = predeccessorMarking.getMarking();
		Integer poppedPosition = predeccessorMarking.getRunPosition();
		final LETTER symbolAtPoppedPosition = mStemAndLoopWord.getSymbol(poppedPosition);
		final Set<ITransition<LETTER, PLACE>> enabledTransitionSet =
				activeTransitionsWithSymbol(poppedMarking, symbolAtPoppedPosition);
		final Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingsOfFireSequence = new HashSet<>();

		for (final ITransition<LETTER, PLACE> transition : enabledTransitionSet) {
			final Marking<LETTER, PLACE> successorMarking = poppedMarking.fireTransition(transition, mOperand);
			Boolean firedIntoAcceptingStateBoolean = false;
			for (PLACE place : mOperand.getSuccessors(transition)) {
				if (mOperand.isAccepting(place)) {
					firedIntoAcceptingStateBoolean = true;
				}
			}
			if (Boolean.TRUE.equals(predeccessorMarking.getAcceptingPlaceSeenInLoopBoolean())) {
				firedIntoAcceptingStateBoolean = true;
			}
			successorMarkingsOfFireSequence.add(
					new MarkingOfFireSequence<>(successorMarking, poppedPosition + 1, firedIntoAcceptingStateBoolean));
		}

		return successorMarkingsOfFireSequence;
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
	 * This method computes if in the given set of markings, there is a marking which is atleast as strong as the given
	 * marking m' we want to compare the set to. <p> A marking m being as strong as a marking m' means for any place p
	 * where m'(p) = n, m(p) >= n has to hold. The reason we do this is if at the end of the supposed loop of a lasso if
	 * the resulting marking is as strong as the hondamarking, we know that we have an actual feasible loop in the Petri
	 * net.
	 * 
	 * @param <markingSet> The set of markings we want to test.
	 * 
	 * @param <comparedMarking> The marking we want to find an as strong marking for.
	 * 
	 * @return boolean representing if a marking of the set is as strong as the comparedMarking.
	 */
	private final Boolean containsStrongerAcceptingMarking(final Set<MarkingOfFireSequence<LETTER, PLACE>> markingSet,
			final Marking<LETTER, PLACE> comparedMarking) {
		final Set<PLACE> comparedMarkingPlaceSet = comparedMarking.stream().collect(Collectors.toSet());
		for (MarkingOfFireSequence<LETTER, PLACE> marking : markingSet) {
			if (marking.getMarking().containsAll(comparedMarkingPlaceSet)
					&& Boolean.TRUE.equals(marking.getAcceptingPlaceSeenInLoopBoolean())) {
				return true;
			}
		}
		return false;
	}
}
