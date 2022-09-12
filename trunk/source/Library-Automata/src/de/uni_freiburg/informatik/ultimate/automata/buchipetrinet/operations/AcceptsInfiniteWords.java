package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract class containing shared methods for the Acceptance classes of Petri nets on infinite words.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public abstract class AcceptsInfiniteWords<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	/**
	 * The Petri net which we check acceptance for.
	 */
	protected final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private final Marking<PLACE> mInitialMarking;
	/**
	 * The word we check acceptance for.
	 */
	private final NestedLassoWord<LETTER> mLassoWord;
	/**
	 * Through nondeterminism in the Petri net one input word can produce multiple different fire sequences. Thus we
	 * could think of the multiple firesequences as a combined fire sequence tree where we have splits when
	 * nondeterministic transitions occur.
	 * <p>
	 * During the traversal of the input word in isWordAcceptedByOmegaNet() mFireSequenceTreeMarkings contains all
	 * markings of the different firing sequences at the current index of the word.
	 */
	protected Set<MarkingOfFireSequence<LETTER, PLACE>> mFireSequenceTreeMarkings;
	/**
	 * Keeps track of the index of the FIreSequenceTree that is created during the isWordAcceptedByOmegaNet() method.
	 */
	protected int mfireSequenceIndex;
	private final boolean mResult;

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
	public AcceptsInfiniteWords(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final NestedLassoWord<LETTER> word)
			throws PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mInitialMarking = new Marking<>(ImmutableSet.of(operand.getInitialPlaces()));
		mLassoWord = word;
		mFireSequenceTreeMarkings = new HashSet<>();
		mfireSequenceIndex = 0;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = isWordAcceptedByOmegaNet();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	protected IPetriNetTransitionProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	/**
	 * Calculates all fire sequences of input word on the Buchi-Petrinet (multiple because of possible nondeterminism of
	 * the net) and checks if one of those fire sequences is accepting.
	 *
	 * @return boolean representing if word is accepted by net.
	 */
	private final boolean isWordAcceptedByOmegaNet() throws PetriNetNot1SafeException {
		computeMarkingsFromFirstWordRun();
		return computeLoopMarkingsAndCheckForAcceptance();
	}

	private void computeMarkingsFromFirstWordRun() throws PetriNetNot1SafeException {
		mFireSequenceTreeMarkings.add(new MarkingOfFireSequence<>(mInitialMarking, new HashSet<>(), 0, 0, 0));
		for (final LETTER symbol : mLassoWord.getStem()) {
			produceSuccessorMarkingsOfFireSequenceOfSet(symbol);
		}
		for (final LETTER symbol : mLassoWord.getLoop()) {
			produceSuccessorMarkingsOfFireSequenceOfSet(symbol);
		}
	}

	// Any time in a firing sequence when the Loop part of a word was fired, we denote the resulting marking as a honda
	// marking. Thus any fire sequence might have multiple hondamarkings.
	private final boolean computeLoopMarkingsAndCheckForAcceptance() throws PetriNetNot1SafeException {
		// TODO: check again for infinite loop edge cases.
		while (!mFireSequenceTreeMarkings.isEmpty()) {
			// After a firing of the Loop part of the word, we store those produced hondamarkings in the firing
			// sequences.
			for (final MarkingOfFireSequence<LETTER, PLACE> marking : mFireSequenceTreeMarkings) {
				marking.addHondaMarkingOfFireSequence(marking.getMarking(), mfireSequenceIndex);
			}
			for (final LETTER symbol : mLassoWord.getLoop()) {
				produceSuccessorMarkingsOfFireSequenceOfSet(symbol);
			}
			// Check if any fire sequence reaches a hondamarking of its stored hondamarkings and if in that loop we fire
			// a token into an accepting Petri place.
			// abstract function checks for acceptance:
			final boolean acceptingConditionsMet = checkForAcceptingConditions();
			if (acceptingConditionsMet) {
				return true;
			}
			for (final Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer> markingAndHondaIndex : containsLoopingFiresequence(
					mFireSequenceTreeMarkings)) {
				if (markingAndHondaIndex.getFirst()
						.getLastIndexOfShootingAcceptingStateInFireSequence() >= markingAndHondaIndex.getSecond()) {
					return true;
				}
				// any nonaccepting firing sequence stuck in a loop is disregarded
				mFireSequenceTreeMarkings.remove(markingAndHondaIndex.getFirst());
			}
		}
		return false;
	}

	abstract boolean checkForAcceptingConditions();

	private void produceSuccessorMarkingsOfFireSequenceOfSet(final LETTER currentSymbol)
			throws PetriNetNot1SafeException {

		final Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingSet = new HashSet<>();
		for (final MarkingOfFireSequence<LETTER, PLACE> markingOfFireSequence : mFireSequenceTreeMarkings) {
			successorMarkingSet.addAll(getSuccessorMarkingsOfFireSequence(markingOfFireSequence, currentSymbol));
		}
		mFireSequenceTreeMarkings = successorMarkingSet;

		mfireSequenceIndex++;
	}

	private Set<MarkingOfFireSequence<LETTER, PLACE>> getSuccessorMarkingsOfFireSequence(
			final MarkingOfFireSequence<LETTER, PLACE> predeccessorMarking, final LETTER currentSymbol)
			throws PetriNetNot1SafeException {

		final Set<Transition<LETTER, PLACE>> enabledTransitionSet =
				activeTransitionsWithSymbol(predeccessorMarking.getMarking(), currentSymbol);

		final Set<MarkingOfFireSequence<LETTER, PLACE>> successorMarkingsOfFireSequence = new HashSet<>();
		for (final Transition<LETTER, PLACE> transition : enabledTransitionSet) {
			successorMarkingsOfFireSequence.add(getSuccessorMarkingOfFireSequence(predeccessorMarking, transition));
		}
		return successorMarkingsOfFireSequence;
	}

	private Set<Transition<LETTER, PLACE>> activeTransitionsWithSymbol(final Marking<PLACE> marking,
			final LETTER symbol) {
		final Set<Transition<LETTER, PLACE>> activeTransitionsWithSymbol = new HashSet<>();
		for (final PLACE place : marking) {
			mOperand.getSuccessors(place).stream().filter(transition -> transition.getSymbol().equals(symbol))
					.filter((transition -> marking.isTransitionEnabled(transition))).collect(Collectors.toSet())
					.forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}

	/**
	 * Creates and returns a {@link MarkingOfFireSequence} containing relevant information regarding the acceptance
	 * conditions, such as if a token was shot into an accepting place, etc.
	 */
	abstract MarkingOfFireSequence<LETTER, PLACE> getSuccessorMarkingOfFireSequence(
			final MarkingOfFireSequence<LETTER, PLACE> predecessor, final Transition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException;

	/**
	 * This method computes if in the given set of markings, there is a marking which is atleast as strong as one honda
	 * marking m' of its fire sequence.
	 * <p>
	 * A marking m being as strong as a marking m' means for any place p where m'(p) = n, m(p) >= n has to hold. The
	 * reason we do this is if at the end of the supposed loop of a lasso if the resulting marking is as strong as the
	 * honda marking, we know that we have an actual feasible loop in the Petri net.
	 *
	 * @param <markingSet>
	 *            The set of markings we want to test.
	 *
	 * @return Pair of marking and the index of the hondamarking they reached.
	 */
	protected final Set<Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer>>
			containsLoopingFiresequence(final Set<MarkingOfFireSequence<LETTER, PLACE>> markingSet) {
		final Set<Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer>> loopingFiringSequences = new HashSet<>();
		for (final MarkingOfFireSequence<LETTER, PLACE> marking : markingSet) {
			for (final Pair<Marking<PLACE>, Integer> hondaMarking : marking.getHondaMarkingsOfFireSequence()) {
				final Set<PLACE> comparedMarkingPlaceSet = hondaMarking.getFirst().stream().collect(Collectors.toSet());
				if (marking.getMarking().containsAll(comparedMarkingPlaceSet)) {
					loopingFiringSequences.add(new Pair<>(marking, hondaMarking.getSecond()));
				}
			}
		}
		return loopingFiringSequences;
	}
}
