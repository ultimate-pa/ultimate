/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collections;
import java.util.Comparator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;

/**
 * Performs persistent set reduction. The goal of this is primarily to reduce the size (in number of states) of the
 * reduced automaton, not so much the language. In particular, {@link MinimalSleepSetReduction} already yields a minimal
 * reduction (in terms of the language), hence persistent sets do not achieve any further reduction in this case.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class PersistentSetReduction<L, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IPersistentSetChoice<L, S> mPersistentSets;

	public PersistentSetReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IPersistentSetChoice<L, S> persistentSets) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Only finite automata are supported";

		mOperand = operand;
		mPersistentSets = persistentSets;
	}

	@Override
	public IStateFactory<S> getStateFactory() {
		return mOperand.getStateFactory();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mOperand.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mOperand.isFinal(state);
	}

	@Override
	public int size() {
		return mOperand.size();
	}

	@Override
	public String sizeInformation() {
		return mOperand.sizeInformation();
	}

	@Override
	public Set<L> lettersInternal(final S state) {
		final var enabled = mOperand.lettersInternal(state);
		final var persistent = mPersistentSets.persistentSet(state);
		return DataStructureUtils.difference(enabled, persistent);
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state) {
		final var persistent = mPersistentSets.persistentSet(state);
		return new FilteredIterable<>(mOperand.internalSuccessors(state), t -> persistent.contains(t.getLetter()));
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		final var persistent = mPersistentSets.persistentSet(state);
		if (persistent.contains(letter)) {
			return mOperand.internalSuccessors(state, letter);
		}
		return Collections.emptyList();
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		return mOperand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		return mOperand.returnSuccessors(state, hier, letter);
	}

	public static <L, S> IDfsOrder<L, S> ensureCompatibility(final IPersistentSetChoice<L, S> persistent,
			final IDfsOrder<L, S> underlying) {
		return new CompatibleDfsOrder<>(persistent, underlying);
	}

	/**
	 * A sleep set order that can be used with persistent set reduction.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the reduced automaton
	 * @param <S>
	 *            The type of states in the reduced automaton
	 */
	private static class CompatibleDfsOrder<L, S> implements IDfsOrder<L, S> {
		private final IPersistentSetChoice<L, S> mPersistent;
		private final IDfsOrder<L, S> mUnderlying;

		public CompatibleDfsOrder(final IPersistentSetChoice<L, S> persistent, final IDfsOrder<L, S> underlying) {
			mPersistent = persistent;
			mUnderlying = underlying;
		}

		@Override
		public Comparator<L> getOrder(final S state) {
			final Set<L> persistent = mPersistent.persistentSet(state);
			final Comparator<L> comparator = mUnderlying.getOrder(state);
			return (a, b) -> {
				if (persistent != null && persistent.contains(a) && !persistent.contains(b)) {
					if (mPersistent.ensuresCompatibility(mUnderlying) && comparator.compare(a, b) >= 0) {
						throw new IllegalStateException("Guarantee of compatibility failed");
					}
					return -1;
				} else if (persistent != null && persistent.contains(b) && !persistent.contains(a)) {
					if (mPersistent.ensuresCompatibility(mUnderlying) && comparator.compare(a, b) <= 0) {
						throw new IllegalStateException("Guarantee of compatibility failed");
					}
					return 1;
				}
				return comparator.compare(a, b);
			};
		}

		@Override
		public boolean isPositional() {
			return mUnderlying.isPositional() || !mPersistent.ensuresCompatibility(mUnderlying);
		}
	}
}
