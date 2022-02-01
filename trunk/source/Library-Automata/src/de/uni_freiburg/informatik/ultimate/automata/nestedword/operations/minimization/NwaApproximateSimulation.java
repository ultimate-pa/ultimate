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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IIncomingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.util.MapBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a nested word automaton, this class computes a binary relation over the states where pairs of states
 * {@code (p, q)} have been removed if clearly {@code q} does not simulate {@code p} according to some simulation
 * definition. The exception is that reflexive pairs are always omitted but should always be present.
 * <p>
 * The result is in general only an overapproximation (if one adds the reflexive pairs) of such a simulation even for
 * finite automata in the presence of nondeterminism. Hence this class is typically used for preprocessing purposes
 * only.
 * <p>
 * This class supports ordinary and direct simulation. For ordinary simulation the state {@code q} must have all
 * outgoing symbols that {@code p} has. Furthermore, for any such symbol {@code a}, among all respective successor
 * states {@code p'} of {@code p} there must be a successor state {@code q'} of {@code q} such that {@code (p', q')} is
 * in the relation.<br>
 * For direct simulation there is the additional constraint that if {@code p} is accepting then {@code q} must also be
 * accepting.
 * <p>
 * This class only considers internal and call transitions (i.e., return transitions are ignored).
 * <p>
 * In short, a pair of states {@code (p, q)} is contained in the output whenever
 * <ul>
 * <li>both states have the same outgoing internal and call symbols,</li>
 * <li>for each common internal and call symbol there is a successor pair {@code (p', q')} in the output</li>
 * <li>(optionally) {@code p} is not accepting or {@code q} is accepting</li>
 * </ul>
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NwaApproximateSimulation<LETTER, STATE>
		extends NwaApproximateXsimulation<LETTER, STATE, Map<STATE, Set<STATE>>> {
	// represents pairs of states; is successively made smaller; does not contain reflexive pairs
	private final Map<STATE, Set<STATE>> mMayBeSimulatedBy;

	// represents pairs of states that have been removed; used for separating the predecessors
	private final HashRelation<STATE, STATE> mIsNotSimulatedBy;

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
	public NwaApproximateSimulation(final AutomataLibraryServices services,
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
	public NwaApproximateSimulation(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand, final SimulationType simulationType,
			final boolean separateByTransitionConstraints) throws AutomataOperationCanceledException {
		super(services, operand);
		mMayBeSimulatedBy = new HashMap<>();
		mIsNotSimulatedBy = new HashRelation<>();

		run(simulationType, separateByTransitionConstraints);

		if (mLogger.isInfoEnabled()) {
			final long numberOfPairs = countNumberOfPairs();
			mLogger.info("Approximate simulation contains " + numberOfPairs + " pairs (excluding reflexive pairs).");
		}
	}

	@Override
	public MapBackedSetOfPairs<STATE> getResult() {
		return new ReflexiveMapBackedSetOfPairs<>(mMayBeSimulatedBy, mOperand.getStates());
	}

	@Override
	protected void initializeAllNonreflexivePairs() throws AutomataOperationCanceledException {
		final ArrayList<STATE> states = new ArrayList<>(mOperand.getStates());
		for (int i = 0; i < states.size(); ++i) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final Set<STATE> rhsStates = new HashSet<>();
			for (int j = 0; j < states.size(); ++j) {
				if (i != j) {
					rhsStates.add(states.get(j));
				}
			}
			mMayBeSimulatedBy.put(states.get(i), rhsStates);
		}
	}

	@Override
	protected void initializeAllNonreflexivePairsRespectingAcceptance() throws AutomataOperationCanceledException {
		final ArrayList<STATE> states = new ArrayList<>(mOperand.getStates());
		for (int i = 0; i < states.size(); ++i) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final Set<STATE> rhsStates = new HashSet<>();
			final STATE lhs = states.get(i);
			if (!mOperand.isFinal(lhs)) {
				rhsStates.addAll(states);
			} else {
				for (int j = 0; j < states.size(); ++j) {
					if (i == j) {
						continue;
					}
					final STATE rhs = states.get(j);
					if (mOperand.isFinal(rhs)) {
						rhsStates.add(rhs);
					} else {
						mIsNotSimulatedBy.addPair(lhs, rhs);
					}
				}
			}
			mMayBeSimulatedBy.put(lhs, rhsStates);
		}
	}

	@Override
	protected void separateByDifferentSymbols() throws AutomataOperationCanceledException {
		final List<STATE> toBeRemoved = new ArrayList<>();
		for (final Entry<STATE, Set<STATE>> entry : mMayBeSimulatedBy.entrySet()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final STATE lhs = entry.getKey();
			final Set<LETTER> lhsInternals = mOperand.lettersInternal(lhs);
			final Set<LETTER> lhsCalls = mOperand.lettersCall(lhs);

			final Set<STATE> rhsStates = entry.getValue();
			final List<STATE> rhsRemove = new ArrayList<>(rhsStates.size());
			for (final STATE rhs : rhsStates) {
				if (mOperand.lettersInternal(rhs).containsAll(lhsInternals)
						&& mOperand.lettersCall(rhs).containsAll(lhsCalls)) {
					// same outgoing symbols
					continue;
				}
				rhsRemove.add(rhs);
			}

			if (rhsRemove.isEmpty()) {
				continue;
			}

			for (final STATE rhs : rhsRemove) {
				rhsStates.remove(rhs);
				mIsNotSimulatedBy.addPair(lhs, rhs);
			}
			if (rhsStates.isEmpty()) {
				toBeRemoved.add(lhs);
			}
		}
		for (final STATE state : toBeRemoved) {
			mMayBeSimulatedBy.remove(state);
		}
	}

	@Override
	protected void separateByTransitionConstraints() throws AutomataOperationCanceledException {
		while (!mIsNotSimulatedBy.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final Entry<STATE, STATE> pair = mIsNotSimulatedBy.iterator().next();
			final STATE lhs = pair.getKey();
			final STATE rhs = pair.getValue();
			mIsNotSimulatedBy.removePair(lhs, rhs);

			for (final LETTER letter : getCommonIncomingLetters(lhs, rhs, mOperand::lettersInternalIncoming)) {
				separatePredecessors(lhs, rhs, state -> mOperand.internalPredecessors(state, letter),
						state -> mOperand.internalSuccessors(state, letter));
			}

			for (final LETTER letter : getCommonIncomingLetters(lhs, rhs, mOperand::lettersCallIncoming)) {
				separatePredecessors(lhs, rhs, state -> mOperand.callPredecessors(state, letter),
						state -> mOperand.callSuccessors(state, letter));
			}
		}
	}

	/**
	 * Given a pair {@code (p', q')} of nonsimulating states, we identify predecessor states {@code (p, q)} under some
	 * letter {@code a} such that the pair {@code (p, q)} is also not in the simulation. For that we search for all
	 * successors {@code q''} of {@code q} under {@code a} and check whether {@code (p', q'')} is in the simulation. If
	 * no such {@code q''} exists, we separate {@code (p, q)}.
	 *
	 * @param lhs
	 *            lhs state of nonsimulating pair.
	 * @param rhs
	 *            rhs state of nonsimulating pair
	 * @param letter2
	 *            common incoming letters
	 * @param predecessorProvider
	 *            function that provides predecessor states for a given state and letter (we know that predecessors
	 *            exist for both states)
	 * @throws AutomataOperationCanceledException
	 *             if operation is canceled
	 */
	private void separatePredecessors(final STATE lhs, final STATE rhs,
			final Function<STATE, Iterable<? extends IIncomingTransitionlet<LETTER, STATE>>> predecessorProvider,
			final Function<STATE, Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>>> successorProvider)
			throws AutomataOperationCanceledException {
		Set<STATE> lhsPossiblySimulatedBy = mMayBeSimulatedBy.get(lhs);
		if (lhsPossiblySimulatedBy == null) {
			lhsPossiblySimulatedBy = Collections.emptySet();
		}
		for (final IIncomingTransitionlet<LETTER, STATE> rhsPredTrans : predecessorProvider.apply(rhs)) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final STATE rhsPred = rhsPredTrans.getPred();
			boolean hasSimulatingNeighbor = false;
			for (final IOutgoingTransitionlet<LETTER, STATE> rhsPredSuccTrans : successorProvider.apply(rhsPred)) {
				final STATE rhsNeighbor = rhsPredSuccTrans.getSucc();
				if ((lhs.equals(rhsNeighbor)) || lhsPossiblySimulatedBy.contains(rhsNeighbor)) {
					hasSimulatingNeighbor = true;
					break;
				}
			}

			if (hasSimulatingNeighbor) {
				continue;
			}

			// no neighbor state of rhs that simulates lhs, i.e., any predecessor of lhs is not simulated
			for (final IIncomingTransitionlet<LETTER, STATE> lhsPredTrans : predecessorProvider.apply(lhs)) {
				separateStates(lhsPredTrans.getPred(), rhsPred);
			}
		}
	}

	private void separateStates(final STATE lhs, final STATE rhs) {
		final Set<STATE> lhsPossiblySimulatedBy = mMayBeSimulatedBy.get(lhs);
		if ((lhsPossiblySimulatedBy != null) && lhsPossiblySimulatedBy.contains(rhs)) {
			lhsPossiblySimulatedBy.remove(rhs);
			if (lhsPossiblySimulatedBy.isEmpty()) {
				mMayBeSimulatedBy.remove(lhs);
			}
			mIsNotSimulatedBy.addPair(lhs, rhs);
		}
	}

	private long countNumberOfPairs() {
		long result = 0;
		for (final Set<STATE> rhs : mMayBeSimulatedBy.values()) {
			result += rhs.size();
		}
		return result;
	}

	/**
	 * Result type that emulates reflexive pairs without storing them.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class ReflexiveMapBackedSetOfPairs<STATE> extends MapBackedSetOfPairs<STATE> {
		private final Set<STATE> mStates;

		public ReflexiveMapBackedSetOfPairs(final Map<STATE, Set<STATE>> map, final Set<STATE> states) {
			super(map);
			mStates = states;
		}

		@Override
		public boolean containsPair(final STATE lhs, final STATE rhs) {
			return lhs.equals(rhs) || super.containsPair(lhs, rhs);
		}

		@Override
		public Iterator<Pair<STATE, STATE>> iterator() {
			final Iterator<Pair<STATE, STATE>> oldIterator = super.iterator();
			final Iterator<STATE> reflexiveIterator = mStates.iterator();
			return new Iterator<Pair<STATE, STATE>>() {
				private boolean reflexiveMode = true;

				@Override
				public boolean hasNext() {
					if (reflexiveMode) {
						if (reflexiveIterator.hasNext()) {
							return true;
						}
						reflexiveMode = false;
					}
					return oldIterator.hasNext();
				}

				@Override
				public Pair<STATE, STATE> next() {
					if (reflexiveMode) {
						assert reflexiveIterator.hasNext();
						final STATE state = reflexiveIterator.next();
						return new Pair<>(state, state);
					}
					assert oldIterator.hasNext();
					return oldIterator.next();
				}
			};
		}

		@Override
		public Map<STATE, Set<STATE>> getRelation() {
			throw new UnsupportedOperationException("The map is not reflexive, hence we do not provide it.");
		}
	}
}
