/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IIncomingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;

/**
 * Given a nested word automaton, this class computes a binary equivalence relation over the states where pairs of
 * states {@code (p, q)} have been removed if clearly {@code q} does not bisimulate {@code p} according to some
 * bisimulation definition. The exception is that reflexive pairs are always omitted but should always be present.
 * <p>
 * The result is in general only an overapproximation (if one adds the reflexive pairs) of such a bisimulation even for
 * finite automata in the presence of nondeterminism. Hence this class is typically used for preprocessing purposes
 * only.
 * <p>
 * This class supports ordinary and direct bisimulation. For ordinary bisimulation the state {@code q} must have all
 * outgoing symbols that {@code p} has. Furthermore, for any such symbol {@code a}, among all respective successor
 * states {@code p'} of {@code p} there must be a successor state {@code q'} of {@code q} such that {@code (p', q')} is
 * in the relation; additionally, the must hold if when swapping {@code p} and {@code q}.<br>
 * For direct bisimulation there is the additional constraint that {@code p} is accepting iff {@code q} is accepting.
 * <p>
 * This class only considers internal and call transitions (i.e., return transitions are ignored).
 * <p>
 * In short, a pair of states {@code (p, q)} is contained in the output whenever
 * <ul>
 * <li>also the pair {@code (q, p)} is in the output,</li>
 * <li>both states have the same outgoing internal and call symbols,</li>
 * <li>for each common internal and call symbol there is a successor pair {@code (p', q')} in the output</li>
 * <li>(optionally) {@code p} is accepting iff {@code q} is accepting</li>
 * </ul>
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NwaApproximateBisimulation<LETTER, STATE>
		extends NwaApproximateXsimulation<LETTER, STATE, Collection<Set<STATE>>> {
	// partition of states that is successively refined
	private final Set<Set<STATE>> mPartition;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param operand
	 *            operand
	 * @param simulationType
	 *            type of simulation
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public NwaApproximateBisimulation(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand, final SimulationType simulationType)
			throws AutomataOperationCanceledException {
		this(services, operand, simulationType, true);
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @param operand
	 *            operand
	 * @param simulationType
	 *            type of simulation
	 * @param separateByTransitionConstraints
	 *            {@code true} iff successor rule should be applied
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public NwaApproximateBisimulation(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand, final SimulationType simulationType,
			final boolean separateByTransitionConstraints) throws AutomataOperationCanceledException {
		this(services, operand, simulationType, createSingleBlockPartition(operand.getStates()),
				separateByTransitionConstraints);
	}

	/**
	 * Constructor with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param simulationType
	 *            type of simulation
	 * @param initialPartition
	 *            initial partition
	 * @param separateByTransitionConstraints
	 *            {@code true} iff successor rule should be applied
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public NwaApproximateBisimulation(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand, final SimulationType simulationType,
			final Collection<Set<STATE>> initialPartition, final boolean separateByTransitionConstraints)
			throws AutomataOperationCanceledException {
		super(services, operand);
		if (initialPartition instanceof Set<?>) {
			mPartition = (Set<Set<STATE>>) initialPartition;
		} else {
			mPartition = new HashSet<>(initialPartition);
		}

		run(simulationType, separateByTransitionConstraints);

		if (mLogger.isInfoEnabled()) {
			final long numberOfPairs = countNumberOfNonreflexivePairs();
			mLogger.info("Approximate bisimulation contains " + numberOfPairs + " pairs (excluding reflexive pairs).");
		}
	}

	@Override
	public PartitionBackedSetOfPairs<STATE> getResult() {
		return new PartitionBackedSetOfPairs<>(mPartition);
	}

	@Override
	protected void initializeAllNonreflexivePairs() throws AutomataOperationCanceledException {
		// do nothing, partition already exists
	}

	@Override
	protected void initializeAllNonreflexivePairsRespectingAcceptance() throws AutomataOperationCanceledException {
		final Collection<Set<STATE>> newBlocks = new ArrayList<>();
		for (final Iterator<Set<STATE>> iter = mPartition.iterator(); iter.hasNext();) {
			final Set<STATE> block = iter.next();
			assert !block.isEmpty() : "The input sets should not be empty.";
			final Set<STATE> finals = new HashSet<>(block.size());
			final Set<STATE> nonfinals = new HashSet<>(block.size());

			for (final STATE state : block) {
				if (mOperand.isFinal(state)) {
					finals.add(state);
				} else {
					nonfinals.add(state);
				}
			}

			// add accepting and nonaccepting blocks if non-empty
			if (!finals.isEmpty() && !nonfinals.isEmpty()) {
				newBlocks.add(finals);
				newBlocks.add(nonfinals);
				iter.remove();
			}
		}
		mPartition.addAll(newBlocks);
	}

	@Override
	protected void separateByDifferentSymbols() throws AutomataOperationCanceledException {
		final Queue<Set<STATE>> queue = new LinkedList<>();
		for (final Set<STATE> block : mPartition) {
			queue.add(block);
		}
		final boolean hasCalls = !mOperand.getVpAlphabet().getCallAlphabet().isEmpty();

		while (!queue.isEmpty()) {
			final Set<STATE> block = queue.poll();

			if (block.size() == 1) {
				continue;
			}

			final boolean splitOccurred = splitBySymbols(block, queue, mOperand::lettersInternal);
			if (hasCalls && !splitOccurred) {
				splitBySymbols(block, queue, mOperand::lettersCall);
			}
		}
	}

	private boolean splitBySymbols(final Set<STATE> block, final Queue<Set<STATE>> queue,
			final Function<STATE, Set<LETTER>> state2letters) {
		// find characteristic sets of letters
		final Map<Set<LETTER>, Set<STATE>> letters2states = new HashMap<>();
		for (final STATE state : block) {
			final Set<LETTER> letters = state2letters.apply(state);
			Set<STATE> states = letters2states.get(letters);
			if (states == null) {
				states = new HashSet<>();
				letters2states.put(letters, states);
			}
			states.add(state);
		}

		if (letters2states.size() == 1) {
			// only one set, nothing happens
			return false;
		}

		// split into new blocks
		mPartition.remove(block);
		for (final Set<STATE> newBlock : letters2states.values()) {
			mPartition.add(newBlock);
			queue.add(newBlock);
		}
		return true;
	}

	@Override
	protected void separateByTransitionConstraints() throws AutomataOperationCanceledException {
		final Queue<Set<STATE>> queue = new LinkedList<>();
		final Map<STATE, Set<STATE>> state2block = new HashMap<>();
		for (final Set<STATE> block : mPartition) {
			queue.add(block);
			for (final STATE state : block) {
				state2block.put(state, block);
			}
		}

		while (!queue.isEmpty()) {
			final Set<STATE> block = queue.poll();

			splitByPredecessors(block, state2block, queue, mOperand::internalPredecessors,
					mOperand::internalPredecessors);

			splitByPredecessors(block, state2block, queue, mOperand::callPredecessors, mOperand::callPredecessors);
		}
	}

	private void splitByPredecessors(final Set<STATE> block, final Map<STATE, Set<STATE>> state2block,
			final Queue<Set<STATE>> queue,
			final Function<STATE, Iterable<? extends ITransitionlet<LETTER, STATE>>> predecessorsState,
			final BiFunction<STATE, LETTER, Iterable<? extends IIncomingTransitionlet<LETTER, STATE>>> predecessors) {
		final Set<LETTER> incomingLetters = getAllTransitionLetters(block, predecessorsState);
		final Set<STATE> marked = new HashSet<>();
		for (final LETTER letter : incomingLetters) {
			// mark all predecessors
			for (final STATE state : block) {
				for (final IIncomingTransitionlet<LETTER, STATE> trans : predecessors.apply(state, letter)) {
					marked.add(trans.getPred());
				}
			}

			// split all marked predecessors
			split(marked, state2block, queue);
		}
	}

	private Set<LETTER> getAllTransitionLetters(final Set<STATE> block,
			final Function<STATE, Iterable<? extends ITransitionlet<LETTER, STATE>>> predecessorProvider) {
		final Set<LETTER> letters = new HashSet<>();
		for (final STATE state : block) {
			for (final ITransitionlet<LETTER, STATE> trans : predecessorProvider.apply(state)) {
				letters.add(trans.getLetter());
			}
		}
		return letters;
	}

	private void split(final Set<STATE> marked, final Map<STATE, Set<STATE>> state2block,
			final Queue<Set<STATE>> queue) {
		while (!marked.isEmpty()) {
			final Iterator<STATE> iterator = marked.iterator();
			final STATE witness = iterator.next();
			iterator.remove();

			splitBlock(witness, marked, state2block, queue);
		}
	}

	private void splitBlock(final STATE witness, final Set<STATE> marked, final Map<STATE, Set<STATE>> state2block,
			final Queue<Set<STATE>> queue) {
		final Set<STATE> block = state2block.get(witness);
		final Set<STATE> markedStatesInBlock = new HashSet<>();
		markedStatesInBlock.add(witness);
		final Set<STATE> unmarkedStatesInBlock = new HashSet<>();
		for (final STATE state : block) {
			if (marked.contains(state)) {
				marked.remove(state);
				markedStatesInBlock.add(state);
			} else if (state != witness) {
				unmarkedStatesInBlock.add(state);
			}
		}
		if (unmarkedStatesInBlock.isEmpty()) {
			// all states were marked, nothing to do
			return;
		}
		mPartition.remove(block);
		updatePartitionAndMap(state2block, markedStatesInBlock);
		updatePartitionAndMap(state2block, unmarkedStatesInBlock);

		// add smaller block to worklist
		if (markedStatesInBlock.size() < unmarkedStatesInBlock.size()) {
			queue.add(markedStatesInBlock);
		} else {
			queue.add(unmarkedStatesInBlock);
		}
	}

	private void updatePartitionAndMap(final Map<STATE, Set<STATE>> state2block, final Set<STATE> newBlock) {
		mPartition.add(newBlock);
		for (final STATE state : newBlock) {
			state2block.put(state, newBlock);
		}
	}

	private static <STATE> Collection<Set<STATE>> createSingleBlockPartition(final Set<STATE> states) {
		final Set<Set<STATE>> result = new HashSet<>();
		result.add(states);
		return result;
	}

	private long countNumberOfNonreflexivePairs() {
		long result = 0;
		for (final Set<STATE> block : mPartition) {
			final long size = block.size();
			result += size * size - size;
		}
		return result;
	}
}
