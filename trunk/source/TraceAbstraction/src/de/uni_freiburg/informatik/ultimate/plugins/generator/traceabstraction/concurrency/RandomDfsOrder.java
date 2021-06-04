/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Comparator;
import java.util.Objects;
import java.util.Random;

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
		mSeed = seed;
		mPositional = positional;
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		return (x, y) -> {
			if (Objects.equals(x, y)) {
				return 0;
			}
			return new Random(getSeed(state, x, y)).nextBoolean() ? -1 : 1;
		};
	}

	private long getSeed(final S state, final L x, final L y) {
		final long seed = mSeed * Objects.hashCode(x) * Objects.hashCode(y);
		if (mPositional) {
			return seed * Objects.hashCode(state);
		}
		return seed;
	}
}
