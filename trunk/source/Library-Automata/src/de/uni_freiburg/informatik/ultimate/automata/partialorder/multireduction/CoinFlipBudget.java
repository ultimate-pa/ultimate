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

public class CoinFlipBudget<L, R> implements IBudgetFunction<L, R> {
	private final IBudgetFunction<L, R> mUnderlying;

	private final Random mRand;
	private final double mProbabilityMin;
	private final boolean mPreemptive;

	public CoinFlipBudget(final boolean preemptive, final long seed, final double probabilityMin,
			final IBudgetFunction<L, R> underlying) {
		mUnderlying = underlying;
		mRand = new Random(seed);
		mProbabilityMin = probabilityMin;
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
		return mRand.nextDouble() >= mProbabilityMin;
	}

	@Override
	public void setReduction(final SleepMapReduction<L, ?, R> reduction) {
		mUnderlying.setReduction(reduction);
	}
}
