/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.ToIntBiFunction;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;

public class OptimisticBudget<L, S, R, V extends IDfsVisitor<L, R>> implements ToIntBiFunction<R, L> {
	private final AutomataLibraryServices mServices;
	private final IDfsOrder<L, R> mOrder;
	private final ISleepMapStateFactory<L, S, R> mStateFactory;
	private final Supplier<V> mMakeVisitor;
	private final Predicate<V> mIsSuccessful;

	private SleepMapReduction<L, S, R> mReduction;

	public OptimisticBudget(final AutomataLibraryServices services, final IDfsOrder<L, R> order,
			final ISleepMapStateFactory<L, S, R> stateFactory, final Supplier<V> makeVisitor,
			final Predicate<V> isSuccessful) {
		mServices = services;
		mOrder = order;
		mStateFactory = stateFactory;
		mMakeVisitor = makeVisitor;
		mIsSuccessful = isSuccessful;
	}

	public void setReduction(final SleepMapReduction<L, S, R> reduction) {
		if (mReduction != null) {
			throw new UnsupportedOperationException("Reduction automaton already set");
		}
		mReduction = reduction;
	}

	@Override
	public int applyAsInt(final R state, final L letter) {
		if (mReduction == null) {
			throw new UnsupportedOperationException(
					"Optimistic budget cannot be used without setting reduction automaton");
		}

		final SleepMap<L, S> sleepMap = mStateFactory.getSleepMap(state);
		int maximumBudget;
		if (sleepMap.contains(letter)) {
			maximumBudget = sleepMap.getPrice(letter);
		} else {
			maximumBudget = mStateFactory.getBudget(state);
		}

		// TODO There are different strategies here:
		// 1) count up from 0 to maximumBudget until successful
		// 2) count down from maximumBudget to 0 while successful
		// 3) binary search!
		for (int budget = 0; budget < maximumBudget; ++budget) {
			final R successor = mReduction.computeSuccessorWithBudget(state, letter, budget);
			if (successor == null) {
				// should not happen in practice
				continue;
			}

			if (isSuccessful(successor)) {
				return budget;
			}
		}

		return maximumBudget;
	}

	private boolean isSuccessful(final R state) {
		// TODO This test will be repeated for the same state many times during the budget determination. Cache it!
		// TODO Caching should take into account monotonicity. Perhaps we can use covering to achieve this.
		final V visitor = mMakeVisitor.get();
		try {
			new DepthFirstTraversal<>(mServices, mReduction, mOrder, visitor, state);
		} catch (final AutomataOperationCanceledException e) {
			throw new IllegalStateException("Could not determine optimistic budget: ", e);
		}
		return mIsSuccessful.test(visitor);
	}
}
