/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
			computeReachableStates(final IRabinAutomaton<LETTER, STATE> automaton) {
		return computeReachableIgnoredStates(automaton, Set.of());
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
			computeReachableIgnoredStates(final IRabinAutomaton<LETTER, STATE> automaton, final Set<STATE> toRemove) {
		final Set<STATE> initialStates = DataStructureUtils.difference(automaton.getInitialStates(), toRemove);
		final Set<STATE> states = new HashSet<>();
		final NestedMap2<STATE, LETTER, Set<STATE>> transitions = new NestedMap2<>();
		final Set<STATE> finiteStates = new HashSet<>();
		final Set<STATE> acceptingStates = new HashSet<>();

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
				final STATE succ = transition.getSucc();
				if (toRemove.contains(succ)) {
					continue;
				}
				final LETTER letter = transition.getLetter();
				Set<STATE> successors = transitions.get(currentState, letter);
				if (successors == null) {
					successors = new HashSet<>();
					transitions.put(currentState, letter, successors);
				}
				successors.add(succ);
				if (!states.contains(succ)) {
					currentStateSet.add(succ);
				}
			}
		}
		return new RabinAutomaton<>(automaton.getAlphabet(), states, initialStates, acceptingStates, finiteStates,
				transitions);
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
	public static <LETTER, STATE> IRabinAutomaton<LETTER, STATE> disjunctiveAutomaton(final Set<LETTER> alphabet,
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
