package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that provides the Rabin acceptance check for (Rabin-)Petri nets.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <PLACE>
 *            Places. Type of the labels ("the content") of the net places.
 */
public final class RabinAcceptsNeu<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final boolean mResult;
	private final IRabinPetriNet<LETTER, PLACE> mOperand;
	private final NestedLassoWord<LETTER> mLassoWord;

	/**
	 * Constructor. Check if given Rabin-Petri Net accepts given word.
	 *
	 * @param services
	 *            Ultimare services.
	 *
	 * @param operand
	 *            Input Petri Net.
	 *
	 * @param word
	 *            Input word.
	 */
	public RabinAcceptsNeu(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final NestedLassoWord<LETTER> word) throws PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLassoWord = word;
		HashSet<Marking<PLACE>> activeMarkings = new HashSet<>();
		activeMarkings.add(new Marking<>(ImmutableSet.of(operand.getInitialPlaces())));
		// compute all markings possible after evaluating the stem of word.
		for (final LETTER symbol : mLassoWord.getStem()) {
			final HashSet<Marking<PLACE>> nextMarkings = new HashSet<>();
			for (final Marking<PLACE> m : activeMarkings) {
				nextMarkings.addAll(getSuccessorMarkings(m, symbol).keySet());
			}
			activeMarkings = nextMarkings;
		}

		mResult = checkForLoop(activeMarkings);

	}

	private boolean checkForLoop(HashSet<Marking<PLACE>> activeMarkings) throws PetriNetNot1SafeException {

		// a index referencing the current letter/position in loop which is to be consumed in this step
		int loopIndex = 0;
		// situations refer to the combination of a state and a letter to be consumed(referenced by loopIndex), if one
		// situation is encountered twice it is not to be evaluated again since its effects/successors are already
		// considered
		final HashSet<Pair<Marking<PLACE>, Integer>> mExploredSituations = new HashSet<>();
		final HashSet<Pair<Marking<PLACE>, Integer>> mAcceptingSituationsWithoutLoop = new HashSet<>();
		while (!activeMarkings.isEmpty()) {
			// if there are no markings reachable with the LassoWord it is not in the language
			final HashSet<Marking<PLACE>> nextMarkings = new HashSet<>();
			final int nextLoopIndex = (loopIndex + 1) % mLassoWord.getLoop().length();
			for (final Marking<PLACE> m : activeMarkings) {

				final Pair<Marking<PLACE>, Integer> preSituation = new Pair<>(m, loopIndex);
				if (mExploredSituations.add(preSituation)) {

					final HashMap<Marking<PLACE>, AcceptanceCondition> reachableMarkings =
							getSuccessorMarkings(m, mLassoWord.getLoop().getSymbol(loopIndex));

					for (final Entry<Marking<PLACE>, AcceptanceCondition> markingWithAcceptanceCondition : reachableMarkings
							.entrySet()) {
						final Pair<Marking<PLACE>, Integer> postSituation =
								new Pair<>(markingWithAcceptanceCondition.getKey(), nextLoopIndex);
						if (markingWithAcceptanceCondition.getValue().equals(AcceptanceCondition.ACCEPTING)
								&& !mAcceptingSituationsWithoutLoop.contains(postSituation)) {

							if (checkForLoop(postSituation)) {
								return true;
							}
							mAcceptingSituationsWithoutLoop.add(postSituation);
						}
						nextMarkings.add(postSituation.getFirst());
					}
				}
			}
			activeMarkings = nextMarkings;

			// for the next step we consider the next letter, if we consumed loop once the next letter will therefore be
			// the one at index 0 of loop, so it can be consumed "infinitely" often
			loopIndex = nextLoopIndex;
		}
		// if there are only non-accepting self loops(no new situations are produced) the automaton does not accept
		return false;

	}

	private boolean checkForLoop(final Pair<Marking<PLACE>, Integer> acceptingSituation)
			throws PetriNetNot1SafeException {
		// situations refer to the combination of a state and a letter to be consumed(referenced by loopIndex), if one
		// situation is encountered twice it is not to be evaluated again since its effects/successors are already
		// considered
		final HashSet<Pair<Marking<PLACE>, Integer>> mExploredSituations = new HashSet<>();
		int loopIndex = acceptingSituation.getSecond();
		HashSet<Marking<PLACE>> activeMarkings = new HashSet<>();
		activeMarkings.add(acceptingSituation.getFirst());
		do {
			// if there are no markings reachable with the LassoWord it is not in the language
			final HashSet<Marking<PLACE>> nextMarkings = new HashSet<>();
			final int nextLoopIndex = (loopIndex + 1) % mLassoWord.getLoop().length();
			for (final Marking<PLACE> m : activeMarkings) {

				if (mExploredSituations.add(new Pair<>(m, loopIndex))) {
					final HashMap<Marking<PLACE>, AcceptanceCondition> reachableMarkings =
							getSuccessorMarkings(m, mLassoWord.getLoop().getSymbol(loopIndex));

					for (final Entry<Marking<PLACE>, AcceptanceCondition> markingWithAcceptanceCondition : reachableMarkings
							.entrySet()) {
						if (!markingWithAcceptanceCondition.getValue().equals(AcceptanceCondition.FINITE)) {
							nextMarkings.add(markingWithAcceptanceCondition.getKey());
							if (markingWithAcceptanceCondition.getValue().equals(AcceptanceCondition.ACCEPTING)
									&& acceptingSituation.equals(
											new Pair<>(markingWithAcceptanceCondition.getKey(), nextLoopIndex))) {
								return true;
							}
						}
					}
				}
			}
			activeMarkings = nextMarkings;

			// for the next step we consider the next letter, if we consumed loop once the next letter will therefore be
			// the one at index 0 of loop, so it can be consumed "infinitely" often
			loopIndex = nextLoopIndex;
		} while (!activeMarkings.isEmpty());

		return false;

	}

	/**
	 * method for returning successor markings and the best AcceptanceCondition which was encountered for all
	 * transitions reaching a specific marking, based on code from Daniel Küchlers RabinAccepts
	 */
	private HashMap<Marking<PLACE>, AcceptanceCondition> getSuccessorMarkings(final Marking<PLACE> predeccessorMarking,
			final LETTER currentSymbol) throws PetriNetNot1SafeException {

		final HashMap<Marking<PLACE>, AcceptanceCondition> result = new HashMap<>();

		final Set<Transition<LETTER, PLACE>> enabledTransitionSet =
				activeTransitionsWithSymbol(predeccessorMarking, currentSymbol);

		for (final Transition<LETTER, PLACE> transition : enabledTransitionSet) {
			AcceptanceCondition ac;
			if (!(transition.getSuccessors().stream().anyMatch(mOperand::isFinite))) {
				if (transition.getSuccessors().stream().anyMatch(mOperand::isAccepting)) {
					ac = AcceptanceCondition.ACCEPTING;
				} else {
					ac = AcceptanceCondition.NONFINITE;
				}
			} else {
				ac = AcceptanceCondition.FINITE;
			}
			final Marking<PLACE> successorMarking = predeccessorMarking.fireTransition(transition);
			if (result.containsKey(successorMarking)) {
				ac = returnBest(result.get(successorMarking), ac);
			}
			result.put(successorMarking, ac);
		}
		return result;
	}

	/**
	 * Copied from Daniel Küchlers Accepts
	 */
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

	private enum AcceptanceCondition {
		FINITE, NONFINITE, ACCEPTING;
	}

	private static AcceptanceCondition returnBest(final AcceptanceCondition x, final AcceptanceCondition y) {
		if (x.ordinal() < y.ordinal()) {
			return y;
		}
		return x;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}
}
