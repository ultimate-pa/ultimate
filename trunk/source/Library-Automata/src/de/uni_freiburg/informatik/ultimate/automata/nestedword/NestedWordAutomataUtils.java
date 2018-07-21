/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.InitialPartitionProcessor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs.PartitionSizeInformation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * Provides static methods that are helpful for working with nested word automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
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
	public static <STATE> long computeNumberOfPairsInPartition(final Collection<Set<STATE>> partition) {
		int result = 0;
		for (final Set<STATE> eqClass : partition) {
			result += eqClass.size() * eqClass.size();
		}
		return result;
	}

	/**
	 * Convert binary relation given as partition into binary relation given as {@link HashRelation}.
	 *
	 * @param <STATE>
	 *            state type
	 */
	public static <STATE> HashRelation<STATE, STATE> constructHashRelation(final AutomataLibraryServices services,
			final Collection<Set<STATE>> partition) throws AutomataOperationCanceledException {
		final HashRelation<STATE, STATE> result = new HashRelation<>();
		final InitialPartitionProcessor<STATE> ipp = new InitialPartitionProcessor<STATE>(services) {

			@Override
			public boolean shouldBeProcessed(final STATE q0, final STATE q1) {
				return true;
			}

			@Override
			public void doProcess(final STATE q0, final STATE q1) {
				result.addPair(q0, q1);
			}
		};
		ipp.process(partition);
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
	public static <LETTER, STATE> String generateGenericMinimizationRunningTaskDescription(final String operationName,
			final INestedWordAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition) {
		final int sizeOfLargestEquivalenceClass =
				NestedWordAutomataUtils.computeSizeOfLargestEquivalenceClass(initialPartition);
		return generateGenericMinimizationRunningTaskDescription(operationName, operand, initialPartition.size(),
				sizeOfLargestEquivalenceClass);
	}

	public static <LETTER, STATE> String generateGenericMinimizationRunningTaskDescription(final String operationName,
			final INestedWordAutomaton<LETTER, STATE> operand, final PartitionSizeInformation initialPartition) {
		return "applying " + operationName + " to NWA with " + operand.size() + " states" + " (initial partition has "
				+ initialPartition.toString() + ")";
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
	public static <LETTER, STATE> String generateGenericMinimizationRunningTaskDescription(final String operationName,
			final INestedWordAutomaton<LETTER, STATE> operand, final int initialPartitionSize,
			final int sizeOfLargestBlock) {
		return "applying " + operationName + " to NWA with " + operand.size() + " states" + " (initial partition has "
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
	 * @param <STATE>
	 *            state type
	 * @return A set of STATEs extracted from iterable.
	 */
	public static <STATE, T> Set<STATE> getStates(final Iterable<T> iterable, final Function<T, STATE> funGetState) {
		return StreamSupport.stream(iterable.spliterator(), false).map(funGetState).collect(Collectors.toSet());
	}

	public static <LETTER, STATE> Set<STATE> constructInternalSuccessors(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa, final STATE state, final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succInternal(state, letter);
		}
		final Function<OutgoingInternalTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.internalSuccessors(state, letter), funGetState);
	}

	public static <LETTER, STATE> Set<STATE> constructCallSuccessors(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa, final STATE state, final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succCall(state, letter);
		}
		final Function<OutgoingCallTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.callSuccessors(state, letter), funGetState);
	}

	public static <LETTER, STATE> Set<STATE> constructReturnSuccessors(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa, final STATE lin, final STATE hier,
			final LETTER letter) {
		if (nwa instanceof NestedWordAutomaton) {
			return ((NestedWordAutomaton<LETTER, STATE>) nwa).succReturn(lin, hier, letter);
		}
		final Function<OutgoingReturnTransition<LETTER, STATE>, STATE> funGetState = t -> t.getSucc();
		return getStates(nwa.returnSuccessors(lin, hier, letter), funGetState);
	}

	/**
	 * @param nwa
	 *            nested word automaton
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return {@code true} iff both the call alphabet and the return alphabet is empty.
	 */
	public static <LETTER, STATE> boolean isFiniteAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		return nwa.getVpAlphabet().getCallAlphabet().isEmpty() && nwa.getVpAlphabet().getReturnAlphabet().isEmpty();
	}

	/**
	 * Checks whether two nested word automata have the same internal, call, and return alphabets.
	 *
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return {@code true} iff the automata have the same alphabets
	 */
	public static <LETTER, STATE> boolean sameAlphabet(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) {
		boolean result;
		result = fstOperand.getVpAlphabet().equals(sndOperand.getVpAlphabet());
		return result;
	}

	/**
	 * Generates a {@link NestedLassoWord} with a given stem and loop length and a random seed.
	 *
	 * @param nwa
	 *            nested word automaton
	 * @param size
	 *            size of the word
	 * @param seed
	 *            seed
	 * @return random {@link NestedLassoWord}
	 */
	public static <LETTER, STATE> NestedLassoWord<LETTER> getRandomNestedLassoWord(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa, final int size, final long seed) {
		final NestedWord<LETTER> stem = (new GetRandomNestedWord<>(null, nwa, size, seed)).getResult();
		final NestedWord<LETTER> loop = (new GetRandomNestedWord<>(null, nwa, size, seed)).getResult();
		return new NestedLassoWord<>(stem, loop);
	}



	/**
	 * @return true iff state has two or more outgoing internal edges that are
	 * labeled with the same letter.
	 */
	private static <LETTER, STATE> boolean isNondeterministicInternal(final STATE state,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersInternal(state)) {
			int numberOfSuccs = 0;
			for (final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator =
					nwa.internalSuccessors(state, letter).iterator(); iterator.hasNext(); iterator.next()) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return true iff state has two or more outgoing call edges that are
	 * labeled with the same letter.
	 */
	private static <LETTER, STATE> boolean isNondeterministicCall(final STATE state,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersCall(state)) {
			int numberOfSuccs = 0;
			for (final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator =
					nwa.callSuccessors(state, letter).iterator(); iterator.hasNext(); iterator.next()) {
				numberOfSuccs++;
				if (numberOfSuccs > 1) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * @return true iff state has two or more outgoing return edges that have the
	 * are the same hierarchical predecessors.
	 */
	private static <LETTER, STATE> boolean isNondeterministicReturn(final STATE state, final STATE hier,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersReturn(state, hier)) {
			int numberOfSuccs = 0;
			for (final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
					nwa.returnSuccessors(state, hier, letter).iterator(); iterator.hasNext(); iterator.next()) {
				numberOfSuccs++;
				if (numberOfSuccs > 1) {
					return true;
				}
			}
		}
		return false;
	}

	public static <LETTER, STATE> boolean isNondeterministic(final STATE up, final STATE down,
			final IDoubleDeckerAutomaton<LETTER, STATE> nwa) {
		final boolean isNondeterministicInternal = isNondeterministicInternal(up, nwa);
		if (isNondeterministicInternal) {
			return true;
		}
		final boolean isNondeterministicCall = isNondeterministicCall(up, nwa);
		if (isNondeterministicCall) {
			return true;
		}
		final boolean isNondeterministicReturn = isNondeterministicReturn(up, down, nwa);
		if (isNondeterministicReturn) {
			return true;
		}
		return false;
	}



	/**
	 * @return Set of all states <tt>hier</tt> such that <tt>state</tt> has an
	 * outgoing return transition
	 * <tt>(state, hier, letter, succ)</tt> for some state <tt>succ</tt>.
	 */
	public static <LETTER, STATE> Set<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter,
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		final Set<STATE> result = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> outRet : nwa.returnSuccessors(state)) {
			if (letter.equals(outRet.getLetter())) {
				result.add(outRet.getHierPred());
			}
		}
		return result;
	}



	/**
	 * @return Iterable over all {@link OutgoingReturnTransition}s of state
	 *         whose LETTER is the letter given as input to this procedure.
	 */
	public static <LETTER, STATE> Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state,
			final LETTER letter, final INestedWordAutomaton<LETTER, STATE> nwa) {
		final Iterable<OutgoingReturnTransition<LETTER, STATE>> iterable = nwa.returnSuccessors(state);
		final Predicate<OutgoingReturnTransition<LETTER, STATE>> remainingElements = x -> x.getLetter().equals(letter);
		return new FilteredIterable<>(iterable, remainingElements);
	}



	public static <LETTER, STATE> Iterable<OutgoingInternalTransition<LETTER, STATE>> constructInternalTransitionIteratorFromNestedMap(
			final STATE state, final LETTER letter, final NestedMap3<STATE, LETTER, STATE, IsContained> internalOut) {
		final Function<STATE, OutgoingInternalTransition<LETTER, STATE>> transformer = x -> new OutgoingInternalTransition<>(letter, x);
		return () -> new TransformIterator<STATE, OutgoingInternalTransition<LETTER, STATE>>(keySetOrEmpty(internalOut.get(state, letter)).iterator(), transformer);
	}

	public static <LETTER, STATE> Iterable<OutgoingCallTransition<LETTER, STATE>> constructCallTransitionIteratorFromNestedMap(
			final STATE state, final LETTER letter, final NestedMap3<STATE, LETTER, STATE, IsContained> callOut) {
		final Function<STATE, OutgoingCallTransition<LETTER, STATE>> transformer = x -> new OutgoingCallTransition<>(letter, x);
		return () -> new TransformIterator<STATE, OutgoingCallTransition<LETTER, STATE>>(keySetOrEmpty(callOut.get(state, letter)).iterator(), transformer);
	}

	public static <LETTER, STATE> Iterable<OutgoingReturnTransition<LETTER, STATE>> constructReturnTransitionIteratorFromNestedMap(
			final STATE state, final STATE hier, final LETTER letter, final NestedMap4<STATE, STATE, LETTER, STATE, IsContained> returnOut) {
		return () -> new TransformIterator<STATE, OutgoingReturnTransition<LETTER, STATE>>(
				keySetOrEmpty(returnOut.get(state, hier, letter)).iterator(), x -> new OutgoingReturnTransition<LETTER, STATE>(hier, letter, x));
	}

	private static <STATE> Iterable<STATE> keySetOrEmpty(final Map<STATE, IsContained> map) {
		if (map == null) {
			return Collections.emptySet();
		} else {
			return map.keySet();
		}
	}

	public static <LETTER> VpAlphabet<LETTER> getVpAlphabet(final IAutomaton<LETTER, ?> automaton) {
		if (automaton instanceof INwaBasis) {
			return ((INwaBasis<LETTER, ?>) automaton).getVpAlphabet();
		} else {
			return new VpAlphabet<>(automaton.getAlphabet());
		}
	}

}
