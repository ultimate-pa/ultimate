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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An independence relation which checks if any condition in a given set of conditions leads to independence of the
 * given letters. For an empty set of conditions, checks for unconditional independence of the given letters.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of conditions
 */
public class DisjunctiveConditionalIndependenceRelation<L, S> implements IIndependenceRelation<Set<S>, L> {
	private final IIndependenceRelation<S, L> mUnderlying;

	/**
	 * Creates a new instance.
	 *
	 * @param underlying
	 *            The underlying relation which is queried for individual conditions. This relation must be conditional.
	 */
	public DisjunctiveConditionalIndependenceRelation(final IIndependenceRelation<S, L> underlying) {
		assert underlying.isConditional() : "Only makes sense for conditional independence relations";
		mUnderlying = underlying;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return true;
	}

	@Override
	public boolean contains(final Set<S> state, final L a, final L b) {
		if (state == null || state.isEmpty()) {
			return mUnderlying.contains(null, a, b);
		}

		for (final S condition : state) {
			if (mUnderlying.contains(condition, a, b)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}
}
