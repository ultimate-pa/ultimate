/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Provides static methods that are helpful for working with nested word automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class NestedWordAutomataUtils {
	private NestedWordAutomataUtils() {
		// prevent instantiation of this class
	}
	
	/**
	 * Applies a function to all direct successors of a state.
	 *
	 * @param operand
	 *            The operand.
	 * @param state
	 *            state
	 * @param consumer
	 *            consumer
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	public static <LETTER, STATE> void applyToReachableSuccessors(final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final STATE state, final Consumer<STATE> consumer) {
		for (final OutgoingInternalTransition<LETTER, STATE> t : operand.internalSuccessors(state)) {
			consumer.accept(t.getSucc());
		}
		for (final OutgoingCallTransition<LETTER, STATE> t : operand.callSuccessors(state)) {
			consumer.accept(t.getSucc());
		}
		for (final OutgoingReturnTransition<LETTER, STATE> t : operand.returnSuccessors(state)) {
			if (operand.isDoubleDecker(state, t.getHierPred())) {
				consumer.accept(t.getSucc());
			}
		}
	}
	
	/**
	 * @param operand
	 *            A double decker automaton.
	 * @param lin
	 *            linear predecessor state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return {@code true} iff operand has a respective outgoing return transition
	 */
	public static <LETTER, STATE> boolean hasOutgoingReturnTransition(
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final STATE lin, final STATE hier,
			final LETTER letter) {
		return operand.returnSuccessors(lin, hier, letter).iterator().hasNext();
	}
	
	/**
	 * @param iterable
	 *            An {@link Iterable} of {@link IOutgoingTransitionlet}.
	 * @param <E>
	 *            transition type
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return the set of all successor states
	 */
	public static <E extends IOutgoingTransitionlet<LETTER, STATE>, LETTER, STATE> Set<STATE>
			constructSuccessorSet(final Iterable<E> iterable) {
		final Set<STATE> result = new HashSet<>();
		for (final E trans : iterable) {
			result.add(trans.getSucc());
			
		}
		return result;
	}
	
	/**
	 * @param partition
	 *            A partition of states.
	 * @param <STATE>
	 *            state type
	 * @return the size of the largest set
	 */
	public static <STATE> int computeSizeOfLargestEquivalenceClass(final Collection<Set<STATE>> partition) {
		int result = 0;
		for (final Set<STATE> eqClass : partition) {
			result = Math.max(result, eqClass.size());
		}
		return result;
	}
	
	/**
	 * @param partition
	 *            A partition of states.
	 * @param <STATE>
	 *            state type
	 * @return the number of pairs of states from within the same blocks
	 */
	public static <STATE> long computeNumberOfEquivalentPairs(final Collection<Set<STATE>> partition) {
		int result = 0;
		for (final Set<STATE> eqClass : partition) {
			result += eqClass.size() * eqClass.size();
		}
		return result;
	}
	
	/**
	 * @param operand
	 *            A nested word automaton.
	 * @param initialPartition
	 *            initial partition
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return string summary of initial partition
	 */
	public static <LETTER, STATE> String generateGenericMinimizationRunningTaskDescription(
			final INestedWordAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition) {
		final int sizeOfLargestEquivalenceClass =
				NestedWordAutomataUtils.computeSizeOfLargestEquivalenceClass(initialPartition);
		return generateGenericMinimizationRunningTaskDescription(operand, initialPartition.size(),
				sizeOfLargestEquivalenceClass);
	}
	
	/**
	 * @param operand
	 *            A nested word automaton.
	 * @param initialPartitionSize
	 *            size of initial partition
	 * @param sizeOfLargestBlock
	 *            size of the largest block in the partition
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return string summary of initial partition
	 */
	public static <LETTER, STATE> String generateGenericMinimizationRunningTaskDescription(
			final INestedWordAutomaton<LETTER, STATE> operand, final int initialPartitionSize,
			final int sizeOfLargestBlock) {
		return "minimizing NWA with " + operand.size() + " states" + " (initial partition has "
				+ initialPartitionSize + " blocks, largest block has " + sizeOfLargestBlock + " states)";
	}
	
	/**
	 * Method that helps converting the return type of {@link INestedWordAutomaton#internalSuccessors(Object)} and the
	 * other similar methods of {@link INestedWordAutomaton} to a {@link Set} of successor states.
	 *
	 * @param iterable
	 *            The return type of, e.g., {@link INestedWordAutomaton#internalSuccessors(Object)}
	 * @param funGetState
	 *            A function that extracts a STATE from an element of iterable
	 * @return A set of STATEs extracted from iterable.
	 */
	public static <STATE, T> Set<STATE> getStates(final Iterable<T> iterable, final Function<T, STATE> funGetState) {
		return StreamSupport.stream(iterable.spliterator(), false).map(funGetState).collect(Collectors.toSet());
	}
	
	public static <LETTER, STATE> Set<STATE> constructInternalSuccessors(
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final STATE state, final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succInternal(state, letter);
		}
		final Function<OutgoingInternalTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.internalSuccessors(state, letter), funGetState);
	}
	
	public static <LETTER, STATE> Set<STATE> constructCallSuccessors(
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final STATE state, final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succCall(state, letter);
		}
		final Function<OutgoingCallTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.callSuccessors(state, letter), funGetState);
	}
	
	public static <LETTER, STATE> Set<STATE> constructReturnSuccessors(
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final STATE lin, final STATE hier,
			final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succReturn(lin, hier, letter);
		}
		final Function<OutgoingReturnTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.returnSuccessors(lin, hier, letter), funGetState);
	}
	
	
	/**
	 * We can consider an NWA empty if call and return alphabet are empty.
	 */
	public static <LETTER, STATE> boolean isFiniteAutomaton(final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		return nwa.getCallAlphabet().isEmpty() && nwa.getReturnAlphabet().isEmpty();
	}
}
