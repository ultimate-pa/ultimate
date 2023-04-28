package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A collection of methods on IRabinAutomaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 */
public class RabinAutomataUtils {

	/**
	 * Removes all states that are not reachable by initialization or traversal of automaton
	 *
	 * @param automaton
	 *            The automaton that should be optimized
	 * @return reduced automaton
	 */
	public static <LETTER, STATE> RabinAutomaton<LETTER, STATE>
			eagerAutomaton(final IRabinAutomaton<LETTER, STATE> automaton) {
		return eagerAutomaton(automaton, Set.of());
	}

	/**
	 * Removes all states that either are:
	 * <ul>
	 * <li>present in toRemove or only reachable from them
	 * <li>not reachable by initialization or traversal of automaton
	 * </ul>
	 *
	 * @param automaton
	 *            The automaton that should be optimized
	 * @param toRemove
	 *            States which should be removed from the resulting Rabin automaton (including (in)direct successors)
	 * @return reduced automaton
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

	/**
	 * A method to compute a general Rabin automaton with multiple accepting sets and corresponding finite sets
	 *
	 * @param <LETTER>
	 *            type of letter
	 * @param <STATE>
	 *            type of state
	 * @param alphabet
	 *            alphabet
	 * @param states
	 *            all states
	 * @param initialStates
	 *            initial states
	 * @param acceptingConditions
	 *            A list of Pairs with first being a list of final states and second being a list of corresponding
	 *            finite states
	 * @param transitions
	 *            transitions
	 * @param factory
	 *            a BlackWhiteStateFactory
	 * @return a parallel automaton that allows multiple different accepting conditions
	 */
	public static <LETTER, STATE> IRabinAutomaton<LETTER, STATE> generalAutomaton(final Set<LETTER> alphabet,
			final Set<STATE> states, final Set<STATE> initialStates,
			final Iterable<Pair<Set<STATE>, Set<STATE>>> acceptingConditions,
			final NestedMap2<STATE, LETTER, Set<STATE>> transitions, final IBlackWhiteStateFactory<STATE> factory) {
		final Iterator<Pair<Set<STATE>, Set<STATE>>> remainingAcceptanceConditions = acceptingConditions.iterator();

		Pair<Set<STATE>, Set<STATE>> temp = remainingAcceptanceConditions.next();

		IRabinAutomaton<LETTER, STATE> result =
				new RabinAutomaton<>(alphabet, states, initialStates, temp.getFirst(), temp.getSecond(), transitions);

		while (remainingAcceptanceConditions.hasNext()) {
			temp = remainingAcceptanceConditions.next();
			result = new RabinUnion<>(result, new RabinAutomaton<>(alphabet, states, initialStates, temp.getFirst(),
					temp.getSecond(), transitions), factory);
		}

		return result;
	}

}
