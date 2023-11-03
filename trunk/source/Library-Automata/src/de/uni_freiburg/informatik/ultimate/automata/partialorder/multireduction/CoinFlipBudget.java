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

import java.util.Random;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;

/**
 * Budget function that flips a random coin to determine if the minimum budget 0 shall be used, or the budget computed
 * by some underlying budget function.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            the type of letters
 * @param <R>
 *            the type of states
 */
public class CoinFlipBudget<L, R> implements IBudgetFunction<L, R> {
	private final IBudgetFunction<L, R> mUnderlying;

	private final Random mRand;
	private final double mProbabilityUnderlying;
	private final boolean mPreemptive;

	/**
	 * Creates a new randomized wrapper for a given underlying budget function.
	 *
	 * @param underlying
	 *            An underlying budget function whose computed budget is used, unless a coin flip determines that it
	 *            shall be overridden with the minimum budget 0.
	 * @param probabilityUnderlying
	 *            Probability that the underlying budget function's value is used, rather than just returning 0.
	 * @param seed
	 *            The seed for the random generator (for reproducible results).
	 * @param preemptive
	 *            If true, the coin flip is made before the computation of the underlying budget function. If the coin
	 *            determines that the minimum budget shall be used, the underlinyg budget function is never called. This
	 *            should usually be set to {@code true}.
	 */
	public CoinFlipBudget(final IBudgetFunction<L, R> underlying, final double probabilityUnderlying, final long seed,
			final boolean preemptive) {
		mUnderlying = underlying;
		mRand = new Random(seed);
		mProbabilityUnderlying = probabilityUnderlying;
		mPreemptive = preemptive;
	}

	@Override
	public int computeBudget(final R state, final L letter) {
		if (mPreemptive && flipCoin()) {
			return 0;
		}
		final int budget = mUnderlying.computeBudget(state, letter);
		if (!mPreemptive && budget > 0 && flipCoin()) {
			return 0;
		}
		return budget;
	}

	private boolean flipCoin() {
		return mRand.nextDouble() >= mProbabilityUnderlying;
	}
}
