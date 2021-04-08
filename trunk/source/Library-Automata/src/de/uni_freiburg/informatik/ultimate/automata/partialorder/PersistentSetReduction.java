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

import java.util.Comparator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;

/**
 * Performs persistent set reduction on top of sleep set reduction. The goal of this is primarily to reduce the size (in
 * number of states) of the reduced automaton, not so much the language. In particular, sleep set reduction with new
 * states already yields a minimal reduction (in terms of the language), hence persistent sets do not achieve any
 * further reduction in this sense. Some further language reduction can possibly be achieved in the delay set case.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class PersistentSetReduction {
	private PersistentSetReduction() {
	}

	public static <L, S, R> void applyNewStateReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<R, L> sleepSetOrder,
			final ISleepSetStateFactory<L, S, R> factory, final IPersistentSetChoice<L, R> persistent,
			final IPartialOrderVisitor<L, R> visitor) throws AutomataOperationCanceledException {
		final ISleepSetOrder<R, L> combinedOrder = new PersistentSleepOrder<>(persistent, sleepSetOrder);
		final IPartialOrderVisitor<L, R> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);
		new SleepSetNewStateReduction<>(services, operand, factory, independenceRelation, combinedOrder,
				combinedVisitor);
	}

	public static <L, S> void applyDelaySetReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final IPersistentSetChoice<L, S> persistent, final IPartialOrderVisitor<L, S> visitor)
			throws AutomataOperationCanceledException {
		final ISleepSetOrder<S, L> combinedOrder = new PersistentSleepOrder<>(persistent, sleepSetOrder);
		final IPartialOrderVisitor<L, S> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);
		new SleepSetDelayReduction<>(services, operand, new ISleepSetStateFactory.NoUnrolling<>(), independenceRelation,
				combinedOrder, combinedVisitor);
	}

	/**
	 * A visitor that performs persistent set reduction by pruning transitions, and proxies non-pruned calls to an
	 * underlying visitor implementation.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the reduced automaton
	 * @param <S>
	 *            The type of states in the reduced automaton
	 */
	private static class PersistentSetVisitor<L, S> implements IPartialOrderVisitor<L, S> {
		private final IPersistentSetChoice<L, S> mPersistent;
		private final IPartialOrderVisitor<L, S> mUnderlying;

		public PersistentSetVisitor(final IPersistentSetChoice<L, S> persistent,
				final IPartialOrderVisitor<L, S> underlying) {
			mPersistent = persistent;
			mUnderlying = underlying;
		}

		@Override
		public void addStartState(final S state) {
			mUnderlying.addStartState(state);
		}

		@Override
		public boolean discoverTransition(final S source, final L letter, final S target) {
			final Set<L> persistent = mPersistent.persistentSet(source);
			if (persistent != null && !persistent.contains(letter)) {
				return true;
			}
			return mUnderlying.discoverTransition(source, letter, target);
		}

		@Override
		public boolean discoverState(final S state) {
			return mUnderlying.discoverState(state);
		}

		@Override
		public void backtrackState(final S state) {
			mUnderlying.backtrackState(state);
		}

		@Override
		public void delayState(final S state) {
			mUnderlying.delayState(state);
		}

		@Override
		public boolean isFinished() {
			return mUnderlying.isFinished();
		}
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
	private static class PersistentSleepOrder<L, S> implements ISleepSetOrder<S, L> {
		private final IPersistentSetChoice<L, S> mPersistent;
		private final ISleepSetOrder<S, L> mUnderlying;

		public PersistentSleepOrder(final IPersistentSetChoice<L, S> persistent,
				final ISleepSetOrder<S, L> underlying) {
			mPersistent = persistent;
			mUnderlying = underlying;
		}

		@Override
		public Comparator<L> getOrder(final S state) {
			final Set<L> persistent = mPersistent.persistentSet(state);
			final Comparator<L> comparator = mUnderlying.getOrder(state);
			return (a, b) -> {
				if (persistent != null && persistent.contains(a) && !persistent.contains(b)) {
					return -1;
				} else if (persistent != null && persistent.contains(b) && !persistent.contains(a)) {
					return 1;
				}
				return comparator.compare(a, b);
			};
		}
	}
}
