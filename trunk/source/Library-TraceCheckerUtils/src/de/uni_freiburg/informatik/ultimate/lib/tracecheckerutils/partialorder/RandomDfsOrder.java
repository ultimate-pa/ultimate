/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.Objects;
import java.util.Random;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;

/**
 * A randomized DFS order. Can be instantiated as positional or non-positional order.
 *
 * Given a fixed seed, the implementation behaves deterministically.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of actions
 * @param <S>
 *            The type of states
 */
public class RandomDfsOrder<L, S> implements IDfsOrder<L, S> {
	private final long mSeed;
	private final boolean mPositional;
	private final Function<S, Object> mNormalizer;

	/**
	 * Creates a new instance.
	 *
	 * @param seed
	 *            The base seed for random values.
	 * @param positional
	 *            Whether or not the created order should be positional, i.e., if the order on letters may depend on the
	 *            state.
	 */
	public RandomDfsOrder(final long seed, final boolean positional) {
		this(seed, positional, null);
	}

	/**
	 * Creates a new instance.
	 *
	 * @param seed
	 *            The base seed for random values.
	 * @param positional
	 *            Whether or not the created order should be positional, i.e., if the order on letters may depend on the
	 *            state.
	 * @param normalizer
	 *            A function mapping a state to some object. States mapped to the same object will get the same order.
	 *            Set to null if not needed, e.g. for non-positional instances.
	 */
	public RandomDfsOrder(final long seed, final boolean positional, final Function<S, Object> normalizer) {
		mSeed = seed;
		mPositional = positional;
		mNormalizer = normalizer;

		assert positional || normalizer == null : "Normalization for non-positional order does not make sense";
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		final long positionalSeed =
				(mPositional && state != null) ? (mSeed * Objects.hashCode(normalize(state))) : mSeed;
		return new RandomComparator<>(positionalSeed);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	@Override
	public boolean isPositional() {
		return mPositional;
	}

	private static class RandomComparator<L> implements Comparator<L> {
		private final long mSeed;

		public RandomComparator(final long seed) {
			mSeed = seed;
		}

		@Override
		public int compare(final L x, final L y) {
			if (x == y) {
				return 0;
			}
			return Integer.compare(getRepresentative(x), getRepresentative(y));
		}

		private int getRepresentative(final L x) {
			return new Random(mSeed * Objects.hashCode(x)).nextInt();
		}

		@Override
		public int hashCode() {
			return Long.hashCode(mSeed);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final RandomComparator<L> other = (RandomComparator<L>) obj;
			return mSeed == other.mSeed;
		}
	}
}
