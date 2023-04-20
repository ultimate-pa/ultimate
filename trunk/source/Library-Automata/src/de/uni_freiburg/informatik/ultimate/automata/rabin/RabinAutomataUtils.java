package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class RabinAutomataUtils {

	/**
	 * Removes all states that are not reachable by initialization or traversal of @param automaton
	 *
	 * @param automaton
	 *            The automaton that should be optimized
	 */
	public static <LETTER, STATE> RabinAutomaton<LETTER, STATE>
			eagerAutomaton(final IRabinAutomaton<LETTER, STATE> automaton) {
		return eagerAutomaton(automaton, Set.of());
	}

	/**
	 * Removes all states that either are:
	 * <ul>
	 * <li>present in @param toRemove or only reachable from them
	 * <li>not reachable by initialization or traversal @param automaton
	 * </ul>
	 *
	 * @param automaton
	 *            The automaton that should be optimized
	 * @param toRemove
	 *            States which should be removed from the resulting Rabin automaton (including (in)direct successors)
	 *
	 */
	public static <LETTER, STATE> RabinAutomaton<LETTER, STATE>
			eagerAutomaton(final IRabinAutomaton<LETTER, STATE> automaton, final Set<STATE> toRemove) {

		final Set<STATE> initialStates = new HashSet<>();
		final Set<STATE> states = new HashSet<>();
		final NestedMap2<STATE, LETTER, Set<STATE>> transitions = new NestedMap2<>();
		final Set<LETTER> alphabet = new HashSet<>();
		final Set<STATE> finiteStates = new HashSet<>();
		final Set<STATE> acceptingStates = new HashSet<>();

		automaton.getInitialStates().forEach(x -> initialStates.add(x));
		initialStates.removeAll(toRemove);

		final ArrayDeque<STATE> currentStateSet = new ArrayDeque<>();
		currentStateSet.addAll(initialStates);

		while (!currentStateSet.isEmpty()) {
			final STATE currentState = currentStateSet.pop();
			states.add(currentState);
			if (automaton.isFinite(currentState)) {
				finiteStates.add(currentState);
			} else if (automaton.isAccepting(currentState)) {
				acceptingStates.add(currentState);
			}

			for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton.getSuccessors(currentState)) {
				if (!toRemove.contains(transition.getSucc())) {

					final LETTER letter = transition.getLetter();
					alphabet.add(letter);
					if (!transitions.containsKey(currentState, letter)) {
						transitions.put(currentState, letter, new HashSet<>());
					}
					transitions.get(currentState, transition.getLetter()).add(transition.getSucc());
					if (!states.contains(transition.getSucc())) {
						currentStateSet.add(transition.getSucc());
					}
				}
			}
		}
		return new RabinAutomaton<>(alphabet, states, initialStates, acceptingStates, finiteStates, transitions);
	}

}
