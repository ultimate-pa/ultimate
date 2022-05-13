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

import java.util.HashMap;
import java.util.Map;
import java.util.function.Predicate;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;

/**
 * Optimistic budget function for {@link SleepMapReduction}: First tries allocating a low budget, and checks if this
 * leads to an undesired automaton (typically, to reaching an accepting state). If so, the budget is increased
 * step-by-step.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the unreduced automaton
 * @param <R>
 *            The type of states in the reduced automaton
 * @param <V>
 *            The type of visitor used to determine if a possible budget choice is desirable
 */
public class OptimisticBudget<L, S, R, V extends IDfsVisitor<L, R>> implements IBudgetFunction<L, R> {
	private final AutomataLibraryServices mServices;
	private final IDfsOrder<L, R> mOrder;
	private final ISleepMapStateFactory<L, S, R> mStateFactory;
	private final Supplier<V> mMakeVisitor;
	private final Predicate<V> mIsSuccessful;

	private SleepMapReduction<L, S, R> mReduction;

	private final Map<R, Boolean> mSuccessCache = new HashMap<>();

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
	public int computeBudget(final R state, final L letter) {
		if (mReduction == null) {
			throw new UnsupportedOperationException(
					"Optimistic budget cannot be used without setting reduction automaton");
		}

		final SleepMap<L, S> sleepMap = mStateFactory.getSleepMap(state);
		int maximumBudget;
		if (sleepMap.contains(letter)) {
			// Never return a budget higher than the price in the sleep map.
			// Because the reduction considers the minimum of the two values, this would be pointless.
			maximumBudget = sleepMap.getPrice(letter);
			assert maximumBudget <= mStateFactory.getBudget(state) : "invalid state: " + state;
		} else {
			// Ensure invariant for budget functions: Must never exceed budget of the current state.
			maximumBudget = mStateFactory.getBudget(state);
		}

		// Find the least budget that is successful.
		for (int budget = 0; budget < maximumBudget; ++budget) {
			final R successor = mReduction.computeSuccessorWithBudget(state, letter, budget);
			if (successor == null) {
				// should not happen in practice
				// (only possible if budget exceeds price in sleep map, but we defined maximumBudget so it would not)
				break;
			}

			if (isSuccessful(successor)) {
				return budget;
			}
		}

		// We fall back to returning the maximum budget.
		return maximumBudget;
	}

	private boolean isSuccessful(final R state) {
		// TODO Caching should take into account monotonicity (if it holds); perhaps use covering to achieve this
		return mSuccessCache.computeIfAbsent(state, this::checkIsSuccessful);
	}

	private boolean checkIsSuccessful(final R state) {
		final V visitor = mMakeVisitor.get();
		try {
			new DepthFirstTraversal<>(mServices, mReduction, mOrder, visitor, state);
		} catch (final AutomataOperationCanceledException e) {
			// TODO turn budget function into an interface that is allowed to throw automata exceptions
			throw new ToolchainCanceledException(getClass());
		}
		return mIsSuccessful.test(visitor);
	}
}
