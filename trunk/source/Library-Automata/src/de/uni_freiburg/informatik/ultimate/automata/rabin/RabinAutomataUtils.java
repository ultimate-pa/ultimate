package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class RabinAutomataUtils {

	/**
	 * Removes all states that either are:
	 * <ul>
	 * <li>not present in the collection State of @param automaton
	 * <li>are not reachable by initialization or traversal @param automaton
	 * </ul>
	 *
	 * @param automaton
	 *            The automaton that should be optimized
	 */
	public static <LETTER, STATE> RabinAutomaton<LETTER, STATE>
			eagerAutomaton(final RabinAutomaton<LETTER, STATE> automaton) {

		final Set<LETTER> mAlphabet;
		final Set<STATE> mStates;
		final Set<STATE> mInitialStates;
		final Set<STATE> mAcceptingStates;
		final Set<STATE> mFiniteStates;
		final NestedMap2<STATE, LETTER, Set<STATE>> mTransitions;

		mInitialStates = new HashSet<>();
		mStates = new HashSet<>();
		mTransitions = new NestedMap2<>();
		mAlphabet = new HashSet<>();
		mFiniteStates = new HashSet<>();
		mAcceptingStates = new HashSet<>();

		automaton.getInitialStates().forEach(x -> mInitialStates.add(x));

		final ArrayDeque<STATE> currentStateSet = new ArrayDeque<>();

		mInitialStates.retainAll(automaton.getStates());

		currentStateSet.addAll(mInitialStates);

		while (!currentStateSet.isEmpty()) {
			final STATE currentState = currentStateSet.pop();
			mStates.add(currentState);
			if (automaton.isFinite(currentState)) {
				mFiniteStates.add(currentState);
			} else if (automaton.isAccepting(currentState)) {
				mAcceptingStates.add(currentState);
			}

			for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton.getSuccessors(currentState)) {
				if (automaton.getStates().contains(transition.getSucc())) {

					final LETTER letter = transition.getLetter();
					mAlphabet.add(letter);
					if (!mTransitions.containsKey(currentState, letter)) {
						mTransitions.put(currentState, letter, new HashSet<>());
					}
					mTransitions.get(currentState, transition.getLetter()).add(transition.getSucc());
					if (!mStates.contains(transition.getSucc())) {
						currentStateSet.add(transition.getSucc());
					}
				}
			}
		}
		return new RabinAutomaton<>(mAlphabet, mStates, mInitialStates, mAcceptingStates, mFiniteStates, mTransitions);
	}

}
